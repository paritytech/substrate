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

fn prefix_ident(ink_def: &InkDef) -> syn::Ident {
	let ink_ident = &ink_def.ident;
	syn::Ident::new(&format!("_GeneratedPrefixForStorage{}", ink_ident), ink_ident.span())
}

pub fn expand_inks(def: &mut Def) -> proc_macro2::TokenStream {
	let frame_support = &def.frame_support;
	let frame_system = &def.frame_system;
	let pallet_ident = &def.pallet_struct.pallet;

    let getters = def.inks.iter().map(|ink_def| {
		let completed_where_clause =
			super::merge_where_clauses(&[&ink_def.where_clause, &def.config.where_clause]);
		let docs = ink_def
			.docs
			.iter()
			.map(|d| quote::quote_spanned!(ink_def.attr_span => #[doc = #d]));


		let ident = &ink_def.ident;
		let gen = &def.type_use_generics(ink_def.attr_span);
		let type_impl_gen = &def.type_impl_generics(ink_def.attr_span);
		let type_use_gen = &def.type_use_generics(ink_def.attr_span);
		let full_ident = quote::quote_spanned!(ink_def.attr_span => #ident<#gen> );
		let cfg_attrs = &ink_def.cfg_attrs;

		let prefix_ident = prefix_ident(ink_def);

		// let item = &mut def.item.content.as_mut().expect("Checked by def").1[ink_def.index];

        // let typ_item = match item {
		// 	syn::Item::Struct(t) => t,
		// 	_ => unreachable!("Checked by def"),
		// };

        println!("Ident {:?}", ink_def.ident);
		let getter = quote::quote!(get_some);

		let v = quote::quote!(SomeFlipper);
		let query = quote::quote!(Option<#ident>);
		let value = quote::quote!(#ident);

		quote::quote_spanned!(ink_def.attr_span =>
			pub type #v<T> = StorageValue<#prefix_ident<#type_use_gen>, #value>;

			#(#cfg_attrs)*
			impl<#type_impl_gen> #pallet_ident<#type_use_gen> #completed_where_clause {
				#( #docs )*
				pub fn #getter() -> #query {
					<
						#v<T> as #frame_support::storage::StorageValue<#value>
					>::get()
				}
			}
		)
    });

	let prefix_structs = def.inks.iter().map(|ink_def| {
		let type_impl_gen = &def.type_impl_generics(ink_def.attr_span);
		let type_use_gen = &def.type_use_generics(ink_def.attr_span);
		let prefix_struct_ident = prefix_ident(ink_def);
		let prefix_struct_vis = &ink_def.vis;
		let prefix_struct_const = ink_def.prefix();
		let config_where_clause = &def.config.where_clause;

		let cfg_attrs = &ink_def.cfg_attrs;

		let maybe_counter = proc_macro2::TokenStream::default();

		quote::quote_spanned!(ink_def.attr_span =>
			#maybe_counter

			#(#cfg_attrs)*
			#[doc(hidden)]
			#prefix_struct_vis struct #prefix_struct_ident<#type_use_gen>(
				core::marker::PhantomData<(#type_use_gen,)>
			);
			#(#cfg_attrs)*
			impl<#type_impl_gen> #frame_support::traits::StorageInstance
				for #prefix_struct_ident<#type_use_gen>
				#config_where_clause
			{
				fn pallet_prefix() -> &'static str {
					<
						<T as #frame_system::Config>::PalletInfo
						as #frame_support::traits::PalletInfo
					>::name::<Pallet<#type_use_gen>>()
						.expect("No name found for the pallet in the runtime! This usually means that the pallet wasn't added to `construct_runtime!`.")
				}
				const STORAGE_PREFIX: &'static str = #prefix_struct_const;
			}
		)
	});

	quote::quote!(
 	   #( #getters )*
		#( #prefix_structs )*
	)
}