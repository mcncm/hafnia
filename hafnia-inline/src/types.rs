//! Macros for moving Rust types across the language interface

use proc_macro::TokenStream;
use quote::quote;
use syn::DeriveInput;

pub fn impl_hafnia_error_macro(_ast: DeriveInput) -> TokenStream {
    let out = quote! {};
    out.into()
}
