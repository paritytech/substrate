// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

use criterion::{Criterion, black_box, Bencher};
use criterion::{criterion_group, criterion_main};
use substrate_state_machine::OverlayedChanges;
use substrate_state_machine::BenchOverlay;

const CONTENT_KEY_SIZE: usize = 32;

fn get_content(seed: u64, len: usize) -> Vec<u8> {
	use rand::SeedableRng;
	use rand::RngCore;
	let mut rng = rand::rngs::SmallRng::seed_from_u64(seed);
	let mut data = vec![0u8; len];
	rng.fill_bytes(&mut data[..]);
	data
}

fn key_val(
	mut inp: &[u8],
	len_key: usize,
	len_val: usize,
) -> Vec<(Vec<u8>, Vec<u8>)> {
	let mut result = Vec::new();
	loop {
		let key = if inp.len() >= len_key {
			inp[..len_key].to_vec()
		} else { break };
		inp = &inp[len_key..];
		let val = if inp.len() >= len_val {
			inp[..len_val].to_vec()
		} else { break };
		inp = &inp[len_val..];
		result.push((key, val));
	}
	result
}

fn commit_drop_commit(b: &mut Bencher, input: &Vec<u8>) {
	let key_vals = key_val(&input[..], 32, 32);
	b.iter(move || {
		let mut overlayed = OverlayedChanges::default();
		for i in key_vals.iter() {
			BenchOverlay(&mut overlayed).bench_set_storage(i.0.clone(), Some(i.1.clone()));
		}
		overlayed.commit_prospective();
		for i in key_vals.iter() {
			BenchOverlay(&mut overlayed).bench_set_storage(i.0.clone(), Some(i.1.clone()));
		}
		overlayed.discard_prospective();
		for i in key_vals.iter() {
			BenchOverlay(&mut overlayed).bench_set_storage(i.0.clone(), Some(i.1.clone()));
		}
		overlayed.commit_prospective();
	});
}

fn commit_drop_commit_and_get(b: &mut Bencher, input: &Vec<u8>) {
	let key_vals = key_val(&input[..], 32, 32);
	b.iter(move || {
		let mut overlayed = OverlayedChanges::default();
		for i in key_vals.iter() {
			BenchOverlay(&mut overlayed).bench_set_storage(i.0.clone(), Some(i.1.clone()));
		}
		for i in key_vals.iter() {
			black_box(overlayed.storage(&i.0));
		}
		overlayed.commit_prospective();
		for i in key_vals.iter() {
			BenchOverlay(&mut overlayed).bench_set_storage(i.0.clone(), Some(i.1.clone()));
		}
		for i in key_vals.iter() {
			black_box(overlayed.storage(&i.0));
		}
		overlayed.discard_prospective();
		for i in key_vals.iter() {
			black_box(overlayed.storage(&i.0));
		}
		for i in key_vals.iter() {
			BenchOverlay(&mut overlayed).bench_set_storage(i.0.clone(), Some(i.1.clone()));
		}
		overlayed.commit_prospective();
	});
}




fn bench_overlay_commit_drop_commit(c: &mut Criterion) {
	let inp = get_content(12, CONTENT_KEY_SIZE * 100);
	let inps = vec![inp];
	c.bench_function_over_inputs("commit_drop_commit", commit_drop_commit, inps);
}
fn bench_overlay_commit_drop_commit_get(c: &mut Criterion) {
	let inp = get_content(12, CONTENT_KEY_SIZE * 100);
	let inps = vec![inp];
	c.bench_function_over_inputs("commit_drop_commit_get", commit_drop_commit_and_get, inps);
}


criterion_group!(benches,
	bench_overlay_commit_drop_commit,
	bench_overlay_commit_drop_commit_get,
);
criterion_main!(benches);
