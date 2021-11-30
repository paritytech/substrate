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

use prometheus_endpoint::{register, CounterVec, Opts, PrometheusError, Registry, U64};

/// We only have a single registered counter metric and se a label to
/// diferentiate between different runtime metrics.
#[derive(Clone)]
pub struct Metrics {
	generic_metric: CounterVec<U64>,
}

/// Runtime metrics wrapper.
#[derive(Clone)]
pub struct RuntimeMetricsProvider(Metrics);

impl RuntimeMetricsProvider {
	pub fn new(metrics_registry: Option<&Registry>) -> Result<Option<Self>, PrometheusError> {
		if let Some(registry) = metrics_registry {
			let metrics = Metrics {
				generic_metric: register(
					CounterVec::new(
						Opts::new("runtime_generic", "Runtime generic metric."),
						&["name"],
					)?,
					registry,
				)?,
			};

			return Ok(Some(Self(metrics)))
		}
		Ok(None)
	}
}

impl sp_core::traits::RuntimeMetrics for RuntimeMetricsProvider {
	fn inc_by(&mut self, name: &str, value: u64) {
		self.0.generic_metric.with_label_values(&[name]).inc_by(value);
	}
}
