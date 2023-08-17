// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use derive_syn_parse::Parse;
use proc_macro2::Span;
use syn::{
	token::{Bracket, Paren},
	Expr, Ident, Item, LitInt, Result, Token,
};

pub mod keywords {
	use syn::custom_keyword;

	custom_keyword!(tasks);
	custom_keyword!(task_list);
	custom_keyword!(condition);
	custom_keyword!(task_index);
	custom_keyword!(pallet);
}

pub struct TasksDef;

impl TasksDef {
	pub fn try_from(_span: Span, _index: usize, _item: &mut Item) -> Result<Self> {
		// TODO: fill in
		Ok(TasksDef {})
	}
}

#[derive(Parse)]
pub enum TaskAttrType {
	#[peek(keywords::task_list, name = "#[pallet::task_list(..)]")]
	TaskList {
		_tasks: keywords::task_list,
		#[paren]
		_paren: Paren,
		#[inside(_paren)]
		expr: Expr,
	},
	#[peek(keywords::task_index, name = "#[pallet::task_index(..)")]
	TaskIndex {
		_task_index: keywords::task_index,
		#[paren]
		_paren: Paren,
		#[inside(_paren)]
		index: LitInt,
	},
	#[peek(keywords::condition, name = "#[pallet::condition(..)")]
	Condition {
		_condition: keywords::condition,
		#[paren]
		_paren: Paren,
		#[inside(_paren)]
		_pipe1: Token![|],
		#[inside(_paren)]
		_ident: Ident,
		#[inside(_paren)]
		_pipe2: Token![|],
		#[inside(_paren)]
		expr: Expr,
	},
	// TODO: Tasks
}

#[derive(Parse)]
pub struct PalletTaskAttr {
	_pound: Token![#],
	#[bracket]
	_bracket: Bracket,
	#[inside(_bracket)]
	_pallet: keywords::pallet,
	#[inside(_bracket)]
	_colons: Token![::],
	#[inside(_bracket)]
	_attr: TaskAttrType,
}

#[cfg(test)]
use syn::parse2;

#[cfg(test)]
use quote::quote;

#[test]
fn test_parse_pallet_task_list_() {
	parse2::<PalletTaskAttr>(quote!(#[pallet::task_list(Something::iter())])).unwrap();
	assert!(parse2::<PalletTaskAttr>(quote!(#[pallet::task_list()])).is_err());
	assert!(parse2::<PalletTaskAttr>(quote!(#[pallet::tasks_list(iter())])).is_err());
	assert!(parse2::<PalletTaskAttr>(quote!(#[pallet::task_list])).is_err());
}

#[test]
fn test_parse_pallet_task_index() {
	parse2::<PalletTaskAttr>(quote!(#[pallet::task_index(3)])).unwrap();
	parse2::<PalletTaskAttr>(quote!(#[pallet::task_index(0)])).unwrap();
	parse2::<PalletTaskAttr>(quote!(#[pallet::task_index(17)])).unwrap();
	assert!(parse2::<PalletTaskAttr>(quote!(#[pallet::task_index])).is_err());
	assert!(parse2::<PalletTaskAttr>(quote!(#[pallet::task_index("hey")])).is_err());
}

#[test]
fn test_parse_pallet_condition() {
	parse2::<PalletTaskAttr>(quote!(#[pallet::condition(|x| x.is_some())])).unwrap();
	parse2::<PalletTaskAttr>(quote!(#[pallet::condition(|_x| some_expr())])).unwrap();
	assert!(parse2::<PalletTaskAttr>(quote!(#[pallet::condition(x.is_some())])).is_err());
	assert!(parse2::<PalletTaskAttr>(quote!(#[pallet::condition(|| something())])).is_err());
}
