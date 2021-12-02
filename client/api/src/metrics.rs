// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Runtime metrics provider.
#![cfg(feature = "runtime_metrics")]

use prometheus_endpoint::{register, CounterVec, Opts, PrometheusError, Registry, U64};
use sp_core::RuntimeMetricLabel;
use std::collections::hash_map::HashMap;

/// We only support CounterVec.
#[derive(Clone, Default)]
pub struct Metrics {
	counter_vecs: HashMap<String, CounterVec<U64>>,
}

/// Runtime metrics wrapper.
#[derive(Clone)]
pub struct RuntimeMetricsProvider(Registry, Metrics);

impl RuntimeMetricsProvider {
	/// Creates new isntance.
	pub fn new(metrics_registry: Option<Registry>) -> Option<Self> {
		if let Some(registry) = metrics_registry {
			return Some(Self(registry, Metrics::default()))
		}
		None
	}

	fn register_countervec(
		&mut self,
		metric_name: &str,
		description: &str,
		label: &RuntimeMetricLabel,
	) -> Result<&mut CounterVec<U64>, PrometheusError> {
		if !self.1.counter_vecs.contains_key(metric_name) {
			let counter_vec = register(
				CounterVec::new(Opts::new(metric_name, description), &[label.as_str()])?,
				&self.0,
			)?;

			self.1.counter_vecs.insert(metric_name.to_owned(), counter_vec);
		}

		// The hashmap is populated above so unwrap() doesn't panic.
		Ok(self.1.counter_vecs.get_mut(metric_name).unwrap())
	}
}

impl sp_core::traits::RuntimeMetrics for RuntimeMetricsProvider {
	fn register_counter(
		&mut self,
		metric_name: &str,
		description: &str,
		label: &RuntimeMetricLabel,
	) {
		let _ = self.register_countervec(metric_name, description, label);
	}

	fn inc_counter_by(&mut self, name: &str, value: u64, label: &RuntimeMetricLabel) {
		let _ = self
			.register_countervec(name, "default description", &RuntimeMetricLabel::from("label"))
			.map_err(|e| )
			.map(|counter| counter.with_label_values(&[label.as_str()]).inc_by(value))
			
	}
}
