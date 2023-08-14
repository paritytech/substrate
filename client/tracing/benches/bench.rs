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

use criterion::{criterion_group, criterion_main, Criterion};
use tracing_subscriber::fmt::time::{ChronoLocal, FormatTime};

fn bench_fast_local_time(c: &mut Criterion) {
	c.bench_function("fast_local_time", |b| {
		let mut buffer = String::new();
		let t = sc_tracing::logging::FastLocalTime { with_fractional: true };
		b.iter(|| {
			buffer.clear();
			t.format_time(&mut buffer).unwrap();
		})
	});
}

// This is here just as a point of comparison.
fn bench_chrono_local(c: &mut Criterion) {
	c.bench_function("chrono_local", |b| {
		let mut buffer = String::new();
		let t = ChronoLocal::with_format("%Y-%m-%d %H:%M:%S%.3f".to_string());
		b.iter(|| {
			buffer.clear();
			t.format_time(&mut buffer).unwrap();
		})
	});
}

criterion_group! {
	name = benches;
	config = Criterion::default();
	targets = bench_fast_local_time, bench_chrono_local
}
criterion_main!(benches);
