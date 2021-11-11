//! This crate contains procedural macros used internally by the Cavy compiler.
//! For the time being, it only contains a convenience macro for building error
//! types, very similar to that found in rustc.

use lazy_static::lazy_static;
use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use regex::Regex;
use std::collections::HashSet;
use syn::{parse_macro_input, punctuated::Punctuated, token::Comma, DeriveInput, Field, Ident};

/// Builds a Cavy error struct implementing Diagnostic. This is supposed to
/// resemble rustc's `SessionDiagnostic` in both form and function.
#[proc_macro_derive(Diagnostic, attributes(msg, span, ctx))]
pub fn diagnostic(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    impl_cavy_error_macro(input)
}

fn impl_cavy_error_macro(ast: DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let DiagnosticData { msg, spans } = DiagnosticData::new(&ast);

    // A list of code snippets for inserting the secondary spans. If they are
    // simple spans, they’re just pushed into the waiting vector of secondaries;
    // if single `Span`s, they're just pushed in, otherwise, that vector is
    // extended.
    //
    // NOTE this won't work if a `Span` is written as *anything other* than
    // literally `Span`. Let's see if that turns out to be a problem.
    let spans_flat = spans.iter().map(|(field, msg)| {
        let ident = field.ident.as_ref().unwrap();
        let msg = match msg {
            Some(msg) => {
                quote! { Some(Box::new(
                    move |f, ctx| {
                        #msg
                    }))
                }
            }
            None => quote! { None },
        };

        match &field.ty {
            syn::Type::Path(p) if p.path.is_ident("Span") => {
                // NOTE this `secondaries` won't have the same type as the one
                // being iterated over in the enclosing loop.
                quote! {
                    spans.push(crate::cavy_errors::SpanReport {
                        span: self.#ident,
                        msg: #msg,
                    });
                }
            }
            _ => {
                quote! {
                    spans.extend(self.#ident.iter().map(|span| {
                        crate::cavy_errors::SpanReport {
                            span: *span,
                            msg: #msg,
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
            fn message(&self, ctx: &crate::context::Context, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                #msg
            }

            fn spans<'a>(&'a self) -> Vec<crate::cavy_errors::SpanReport<'a>> {
                // Here we've been given a bunch of fields, each of which might
                // be a single `Span` or a `Vec` of them. We'll have to look at
                // the type of the field to decide how to flatten the regions
                // list.
                let mut spans = Vec::new();
                #(
                    #spans_flat
                )*
                spans
            }

            fn error_code(&self) -> &str {
                "error [E000]"
            }
        }
    };

    expanded.into()
}

/// A literal message with some struct fields interpolated into it
struct InterpolatedMessage<'ast> {
    /// The mssage itself
    msg: syn::Lit,
    /// Fields that are referenced in the format string and must be formatted with a context
    ctx_fields: Vec<&'ast syn::Ident>,
    /// Fields that are referenced in the format string and can be formatted with `fmt::Display`
    dis_fields: Vec<&'ast syn::Ident>,
}

impl<'ast> ToTokens for InterpolatedMessage<'ast> {
    fn to_tokens(&self, tokens: &mut quote::__private::TokenStream) {
        let dis_fields = &self.dis_fields;
        let ctx_fields = &self.ctx_fields;
        let msg = &self.msg;
        let new_tokens = quote! {
                write!(
                    f,
                    #msg,
                #(#dis_fields = self.#dis_fields,)*
                #(#ctx_fields = crate::util::FmtWith::fmt_with(&self.#ctx_fields, &ctx),)*
            )
        };
        new_tokens.to_tokens(tokens);
    }
}

/// A data structure representing the analyzed struct, whose members are used to
/// build up the ultimate Diagnostic struct.
struct DiagnosticData<'ast> {
    /// The message reported by the error, which should refer to the main span
    msg: InterpolatedMessage<'ast>,
    /// Source spans that should be reported with the error
    spans: Vec<(&'ast syn::Field, Option<InterpolatedMessage<'ast>>)>,
}

/// Check if a given field has a helper attribute.
fn has_attr(field: &syn::Field, expected: &str) -> bool {
    field.attrs.iter().any(|attr| attr.path.is_ident(expected))
}

impl<'ast> DiagnosticData<'ast> {
    /// Used by `new` when interpreting attributes
    fn handle_meta(
        field: &'ast syn::Field,
        attr: &'ast syn::Attribute,
        spans: &mut Vec<(&'ast syn::Field, Option<syn::Lit>)>,
    ) {
        let meta = attr
            .parse_meta()
            .expect("malformed attribute in diagnostic");

        if meta.path().segments[0].ident == "span" {
            let mut msg = None;
            if let syn::Meta::List(list) = meta {
                for elem in list.nested {
                    if let syn::NestedMeta::Meta(syn::Meta::NameValue(nv)) = elem {
                        let key = &nv.path.segments[0].ident;
                        if nv.path.segments.len() == 1 && key == "msg" {
                            msg = Some(nv.lit);
                        }
                    }
                }
            }
            spans.push((field, msg))
        }
    }

    fn get_msg(ast: &'ast DeriveInput) -> syn::Lit {
        for attr in ast.attrs.iter() {
            let meta = attr.parse_meta().unwrap();
            if let syn::Meta::NameValue(nv) = meta {
                let key = &nv.path.segments[0].ident;
                if nv.path.segments.len() == 1 && key == "msg" {
                    return nv.lit;
                }
            }
        }
        panic!("Expected an error message");
    }

    fn new(ast: &'ast DeriveInput) -> Self {
        // Like in rustc, any error should come with a span that is indicated
        // in the error report.
        let mut spans = Vec::new();

        let fields = if let syn::Data::Struct(syn::DataStruct {
            fields: syn::Fields::Named(syn::FieldsNamed { named, .. }),
            ..
        }) = &ast.data
        {
            named
        } else {
            panic!("tried to derive diagnostic on a malformed struct")
        };

        // NOTE: Is there a simpler way to do this, like with
        // `attr.path.is_ident` above?
        for field in fields.iter() {
            for attr in &field.attrs {
                Self::handle_meta(field, attr, &mut spans);
            }
        }

        let msg = Self::get_msg(ast);
        let (ctx_fields, dis_fields) = Self::fmt_fields(msg.clone(), fields);

        let msg = InterpolatedMessage {
            msg,
            ctx_fields,
            dis_fields,
        };

        let spans: Vec<_> = spans
            .into_iter()
            .map(|(span, msg)| {
                let msg = msg.map(|msg| {
                    let (ctx_fields, dis_fields) = Self::fmt_fields(msg.clone(), fields);
                    InterpolatedMessage {
                        msg,
                        ctx_fields,
                        dis_fields,
                    }
                });
                (span, msg)
            })
            .collect();

        assert!(!spans.is_empty(), "Must report at least one span");

        Self { msg, spans }
    }

    /// Get the names of fields that should be interpolated into a given message.
    fn fmt_fields(msg: syn::Lit, fields: &Punctuated<Field, Comma>) -> (Vec<&Ident>, Vec<&Ident>) {
        // Identify which fields are interpolated into this message
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

        (ctx_fields, dis_fields)
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
