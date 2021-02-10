//! This crate contains procedural macros used internally by the Cavy compiler.
//! For the time being, it only contains a convenience macro for building error
//! types, very similar to that found in rustc.

use lazy_static::lazy_static;
use proc_macro::TokenStream;
use quote::quote;
use regex::Regex;
use std::collections::HashSet;
use syn::{parse_macro_input, DeriveInput};

/// Builds a Cavy error struct implementing Diagnostic. This is supposed to
/// resemble rustc's `SessionDiagnostic` in both form and function.
#[proc_macro_derive(Diagnostic, attributes(msg, ctx))]
pub fn diagnostic(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    impl_cavy_error_macro(input)
}

fn impl_cavy_error_macro(ast: DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let DiagnosticData {
        main_span,
        msg,
        ctx_fields,
        dis_fields,
    } = DiagnosticData::new(&ast);

    let expanded = quote! {
        impl std::fmt::Debug for #name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "error")
            }
        }

        impl crate::cavy_errors::Diagnostic for #name {
            /// Can I do this without making an owned string?
            fn message(&self, ctx: &crate::context::Context) -> String {
                format!(
                    #msg,
                    #(#dis_fields = self.#dis_fields,)*
                    #(#ctx_fields = crate::context::CtxDisplay::fmt_with(&self.#ctx_fields, &ctx),)*
                )
            }

            fn main_span(&self) -> &crate::source::Span {
                &self.#main_span
            }

            fn code(&self) -> &str {
                "error [E000]"
            }
        }
    };

    expanded.into()
}

/// A data structure representing the analyzed struct, whose members are used to
/// build up the ultimate Diagnostic struct.
struct DiagnosticData<'ast> {
    /// The message reported by the error, which should refer to the main span
    msg: syn::Lit,
    /// The main span that should be reported with the error
    #[allow(unused)]
    main_span: &'ast syn::Ident,
    /// Fields that are referenced in the format string and must be formatted with a context
    ctx_fields: Vec<&'ast syn::Ident>,
    /// Fields that are referenced in the format string and can be formatted with `fmt::Display`
    dis_fields: Vec<&'ast syn::Ident>,
}

/// Check if a given field has a helper attribute.
fn has_attr(field: &syn::Field, expected: &str) -> bool {
    field.attrs.iter().any(|attr| attr.path.is_ident(expected))
}

impl<'ast> DiagnosticData<'ast> {
    fn new(ast: &'ast DeriveInput) -> Self {
        // Like in rustc, any error should come with a span that is indicated
        // in the error report.
        let mut main_span = None;
        let mut msg = None;

        let fields = if let syn::Data::Struct(syn::DataStruct {
            fields: syn::Fields::Named(syn::FieldsNamed { named, .. }),
            ..
        }) = &ast.data
        {
            named
        } else {
            panic!("tried to derive diagnostic on a malformed struct")
        };

        // Find the main span and message from among the fields. The main span
        // must be annotated with the "msg" helper attribute.
        //
        // NOTE: Is there a simpler way to do this, like with
        // `attr.path.is_ident` above?
        for field in fields.iter() {
            for attr in &field.attrs {
                let meta = attr
                    .parse_meta()
                    .expect("malformed attribute in diagnostic");
                if let syn::Meta::NameValue(nv) = meta {
                    let ident = &nv.path.segments[0].ident;
                    if nv.path.segments.len() == 1 && ident == "msg" {
                        if main_span.is_none() {
                            msg = Some(nv.lit);
                            // Should we check that the type is Span?
                            main_span = Some(field.ident.as_ref().unwrap());
                        } else {
                            panic!("two main spans in diagnostic");
                        }
                    }
                };
            }
        }

        let msg = msg.expect("no message or main span in diagnostic");
        let main_span = main_span.unwrap();
        // Get a set of &str naming the fields to be formatted
        let fmt_fields = Self::find_fmt_fields(&msg);
        // Now we iterate through the fields again, this time in order to split
        // up the `HashSet<&str>` to a pair of `Vec<syn::Ident>` of the actual
        // struct members. The first vector consists of the format fields that
        // need to be formatted with a context; the second is those that simply
        // implement Display.
        let (ctx_fields, dis_fields): (Vec<_>, Vec<_>) = fields
            .iter()
            // Take only the ones that were in the `fmt_fields` list
            .filter(|field| {
                let ident = field.ident.as_ref().unwrap();
                fmt_fields.contains(ident.to_string().as_str())
            })
            // And split them up according to whether or not they must be
            // formatted with a context
            .partition(|field| has_attr(field, "ctx"));

        // Can I make this *at all* less repetitive?
        let ctx_fields = ctx_fields
            .iter()
            .map(|field| field.ident.as_ref().unwrap())
            .collect();
        let dis_fields = dis_fields
            .iter()
            .map(|field| field.ident.as_ref().unwrap())
            .collect();

        Self {
            main_span,
            msg,
            ctx_fields,
            dis_fields,
        }
    }

    /// Parses the message for set of all the fields that are to be formatted
    ///
    /// There are some ownership issues in here. I’d like to return a
    /// HashSet<&str>, if possible.
    fn find_fmt_fields(msg: &syn::Lit) -> HashSet<String> {
        lazy_static! {
            // Matches alphanumeric substrings within literal braces.
            static ref RE: Regex = Regex::new(r"\{(\w+)\}").unwrap();
        }

        let msg = match msg {
            syn::Lit::Str(s) => s.value(),
            _ => panic!("diagnostic message is not a string literal"),
        };
        RE.captures_iter(&msg)
            .map(|grp| grp.get(1).unwrap().as_str().to_owned())
            .collect()
    }
}
