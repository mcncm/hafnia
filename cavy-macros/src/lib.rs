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
#[proc_macro_derive(Diagnostic, attributes(msg, ctx, secondary, help))]
pub fn diagnostic(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    impl_cavy_error_macro(input)
}

fn impl_cavy_error_macro(ast: DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let DiagnosticData {
        main_span,
        secondaries,
        msg,
        ctx_fields,
        dis_fields,
    } = DiagnosticData::new(&ast);

    // FIXME ignore the optional message
    let main_span = main_span.0.ident.as_ref().unwrap();

    // A list of code snippets for inserting the secondary spans. If they are
    // simple spans, they’re just pushed into the waiting vector of secondaries;
    // if single `Span`s, they're just pushed in, otherwise, that vector is
    // extended.
    //
    // NOTE this won't work if a `Span` is written as *anything other* than
    // literally `Span`. Let's see if that turns out to be a problem.
    let secondaries_flat = secondaries.iter().map(|(field, help)| {
        let ident = field.ident.as_ref().unwrap();
        let help = match help {
            Some(help) => quote! { Some(#help) },
            None => quote! { None },
        };

        match &field.ty {
            syn::Type::Path(p) if p.path.is_ident("Span") => {
                // NOTE this `secondaries` won't have the same type as the one
                // being iterated over in the enclosing loop.
                quote! {
                    secondaries.push(crate::cavy_errors::RegionReport {
                        span: self.#ident,
                        help: #help,
                    });
                }
            }
            _ => {
                quote! {
                    secondaries.extend(self.#ident.iter().map(|span| {
                        crate::cavy_errors::RegionReport {
                            span: *span,
                            help: #help,
                        }
                    }));
                }
            }
        }
    });

    let expanded = quote! {
        impl std::fmt::Debug for #name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "error")
            }
        }

        impl crate::cavy_errors::Diagnostic for #name {
            // Can I do this without making an owned string?
            fn message(&self, ctx: &crate::context::Context) -> String {
                format!(
                    #msg,
                    #(#dis_fields = self.#dis_fields,)*
                    #(#ctx_fields = crate::context::CtxDisplay::fmt_with(&self.#ctx_fields, &ctx),)*
                )
            }

            fn main_span(&self) -> crate::cavy_errors::RegionReport {
                crate::cavy_errors::RegionReport {
                    span: self.#main_span,
                    help: None,
                }
            }

            fn secondaries(&self) -> Vec<crate::cavy_errors::RegionReport> {
                // Here we've been given a bunch of fields, each of which might
                // be a single `Span` or a `Vec` of them. We'll have to look at
                // the type of the field to decide how to flatten the regions
                // list.
                let mut secondaries = Vec::new();
                #(
                    #secondaries_flat
                )*
                secondaries
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
    main_span: (&'ast syn::Field, Option<syn::Lit>),
    /// Secondary spans to be reported. They come as a pair of a field with,
    /// optionally, a help message.
    secondaries: Vec<(&'ast syn::Field, Option<syn::Lit>)>,
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
        let mut secondaries = Vec::new();
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
                match meta {
                    syn::Meta::NameValue(nv) => {
                        let ident = &nv.path.segments[0].ident;
                        if nv.path.segments.len() == 1 && ident == "msg" {
                            if main_span.is_none() {
                                msg = Some(nv.lit);
                                // Should we check that the type is Span?
                                main_span = Some((field, None));
                            } else {
                                panic!("two main spans in diagnostic");
                            }
                        // This is a stopgap. It might be best to make no
                        // special distinction between primary and secondary
                        // spans, and have a separate attribute for the main
                        // message.
                        } else if nv.path.segments.len() == 1 && ident == "help" {
                            secondaries.push((field, Some(nv.lit)));
                        }
                    }
                    syn::Meta::Path(path) => {
                        let ident = &path.segments[0].ident;
                        if path.segments.len() == 1 && ident == "secondary" {
                            secondaries.push((field, None));
                        }
                    }
                    syn::Meta::List(_) => {
                        panic!("not sure what to do in this case")
                    }
                }
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
            secondaries,
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
