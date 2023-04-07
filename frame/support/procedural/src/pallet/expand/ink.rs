use crate::{
	counter_prefix,
	pallet::{
		parse::ink::{InkDef},
		Def,
	},
};
use quote::ToTokens;
use std::{collections::HashMap, ops::IndexMut};
use syn::spanned::Spanned;

pub fn expand_inks(def: &mut Def) -> proc_macro2::TokenStream {
    for ink_def in def.inks.iter_mut() {
		let item = &mut def.item.content.as_mut().expect("Checked by def").1[ink_def.index];

        let typ_item = match item {
			syn::Item::Struct(t) => t,
			_ => unreachable!("Checked by def"),
		};

        println!("{:?}", typ_item);

    }

    quote::quote!(
    )
}