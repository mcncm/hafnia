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
#[proc_macro_derive(Diagnostic, attributes(msg))]
pub fn diagnostic(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    impl_cavy_error_macro(input)
}

fn impl_cavy_error_macro(ast: DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let DiagnosticData {
        main_span,
        msg,
        fmt_fields,
    } = DiagnosticData::new(&ast);

    let expanded = quote! {
        impl std::fmt::Debug for #name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "error")
            }
        }

        impl Diagnostic for #name {
            fn message(&self) -> String {
                format!(#msg, #(#fmt_fields = self.#fmt_fields,)*)
            }

            fn main_span(&self) -> &Span {
                &self.#main_span
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
    /// Fields that are referenced in the format string
    fmt_fields: Vec<&'ast syn::Ident>,
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

        // Find the main span and message from among the fields
        for field in fields.iter() {
            for attr in &field.attrs {
                let meta = attr
                    .parse_meta()
                    .expect("malformed attribute in diagnostic");
                match meta {
                    syn::Meta::NameValue(nv) => {
                        let ident = &nv.path.segments[0].ident;
                        if nv.path.segments.len() == 1 && ident == "msg" {
                            if let None = main_span {
                                msg = Some(nv.lit);
                                // Should we check that the type is Span?
                                main_span = Some(field.ident.as_ref().unwrap());
                            } else {
                                panic!("two main spans in diagnostic");
                            }
                        }
                    }
                    _ => panic!("unexpected attribute in diagnostic"),
                };
            }
        }

        let msg = msg.expect("no message or main span in diagnostic");
        let main_span = main_span.unwrap();
        // Get a set of &str naming the fields to be formatted
        let fmt_fields = Self::find_fmt_fields(&msg);
        // Now we iterate through the fields again, this time in order to shadow
        // fmt_fields from a HashSet<&str> to a Vec<syn::Ident> of the actual
        // struct members.
        let fmt_fields = fields
            .iter()
            .filter_map(|field| {
                let ident = field.ident.as_ref().unwrap();
                if fmt_fields.contains(ident.to_string().as_str()) {
                    Some(ident)
                } else {
                    None
                }
            })
            .collect();

        Self {
            main_span,
            msg,
            fmt_fields,
        }
    }

    /// Returns the set of all the fields that are formatted.
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
