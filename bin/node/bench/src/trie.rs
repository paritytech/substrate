// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Trie benchmark (integrated).

use std::borrow::Cow;
use crate::{
	core::{self, Path},
	generator::generate_trie,
	tempdb::TempDatabase,
};

#[derive(Clone, Copy, Debug, derive_more::Display)]
pub enum DatabaseSize {
	Empty,
	Smallest,
	Small,
	Medium,
	Large,
	Largest,
}

impl DatabaseSize {
	fn keys(&self) -> usize {
		match *self {
			Self::Empty => 10, // still need some keys
			Self::Smallest => 100,
			Self::Small => 1_000,
			Self::Medium => 10_000,
			Self::Large => 100_000,
			Self::Largest => 1_000_000,
		}
	}
}

pub struct TrieBenchmarkDescription {
	pub database_size: DatabaseSize,
}

pub struct TrieBenchmark {
	database_size: DatabaseSize,
}

impl core::BenchmarkDescription for TrieBenchmarkDescription {
	fn path(&self) -> Path {
		let mut path = Path::new(&["trie"]);

		match self.database_size {
			DatabaseSize::Empty => path.push("empty"),
			DatabaseSize::Smallest => path.push("smallest"),
			DatabaseSize::Small => path.push("small"),
			DatabaseSize::Medium => path.push("medium"),
			DatabaseSize::Large => path.push("large"),
			DatabaseSize::Largest => path.push("largest"),
		}

		path
	}

	fn setup(self: Box<Self>) -> Box<dyn core::Benchmark> {
		Box::new(TrieBenchmark { database_size: self.database_size })
	}

	fn name(&self) -> Cow<'static, str> {
		format!(
			"Trie benchmark({:?} database)",
			self.database_size,
		).into()
	}
}

impl core::Benchmark for TrieBenchmark {
	fn run(&mut self) -> std::time::Duration {
		unimplemented!()
	}
}