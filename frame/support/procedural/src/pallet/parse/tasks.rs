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
use syn::{
	token::{Bracket, Paren},
	Expr, Ident, LitInt, Token,
};

pub mod keywords {
	use syn::custom_keyword;

	custom_keyword!(tasks);
	custom_keyword!(condition);
	custom_keyword!(task_index);
	custom_keyword!(pallet);
}

#[derive(Parse)]
pub enum TaskAttrType {
	#[peek(keywords::tasks, name = "#[pallet::tasks(..)]")]
	Tasks {
		_tasks: keywords::tasks,
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
	attr: TaskAttrType,
}
