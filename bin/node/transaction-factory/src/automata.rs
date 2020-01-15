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

//! Implementation of a kind of automata, used to read benchmark tests from files.

use std::env;
use std::fs;
use std::collections::HashMap;

#[derive(Debug)]
pub struct Edge {
	target: u32,
	tx_name: String,
	priority: u32,
	repeat: u32,
	used: u32, 
}

#[derive(Debug)]
pub struct Node {
	outputs: Vec<Edge>,
}

#[derive(Debug)]
pub struct Automaton {
	nodes: HashMap<u32, Node>,
	current_node: u32,
}

impl Automaton {
	pub fn new() -> Self {
		Self {
			nodes: HashMap::new(),
			current_node: 0,
		}
	}

	pub fn new_from_file(file_name_path: String) -> Self {
		let contents = fs::read_to_string(file_name_path)
			.expect("something went wrong reading the bench file");
		let mut automaton = Automaton::new();
		
		for line in contents.lines() {
			let line: Vec<&str> = line.split_whitespace().collect();
			let source = line[0].parse().expect("source value can't be parsed");
			let target = line[1].parse().expect("target value can't be parsed");
			let tx_name = line[2].to_string();
			let repeat = line[3].parse().expect("repeat value can't be parsed");
			let priority = line[4].parse().expect("priority value can't be parsed");

			let edge = Edge {
				target,
				tx_name,
				priority,
				repeat,
				used: 0,
			};

			if let Some(node) = automaton.nodes.get_mut(&source) {
				node.outputs.push(edge);
			} else {
				let new_node = Node { outputs: vec![edge] };
				automaton.nodes.insert(source, new_node);
			}
		}

		automaton
	}

	pub fn next_state(&mut self) -> Option<String> {
		if let Some(node) = self.nodes.get_mut(&self.current_node) {
			let mut max_priority_output = node.outputs.first_mut().expect("TODO");

			self.current_node = max_priority_output.target;
			max_priority_output.used += 1;

			Some(max_priority_output.tx_name.clone())
		} else {
			panic!("automaton current state is undefined, check your bench file!");
		}
	}
}

