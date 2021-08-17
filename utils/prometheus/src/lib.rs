// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

#[cfg(not(target_os = "unknown"))]
use futures_util::future::Future;
use prometheus::core::Collector;
pub use prometheus::{
	self,
	core::{
		AtomicF64 as F64, AtomicI64 as I64, AtomicU64 as U64, GenericCounter as Counter,
		GenericCounterVec as CounterVec, GenericGauge as Gauge, GenericGaugeVec as GaugeVec,
	},
	exponential_buckets, Error as PrometheusError, Histogram, HistogramOpts, HistogramVec, Opts,
	Registry,
};
#[cfg(not(target_os = "unknown"))]
use prometheus::{Encoder, TextEncoder};
use std::net::SocketAddr;

#[cfg(not(target_os = "unknown"))]
mod networking;
mod sourced;

pub use sourced::{MetricSource, SourcedCounter, SourcedGauge, SourcedMetric};

#[cfg(not(target_os = "unknown"))]
pub use known_os::init_prometheus;
#[cfg(target_os = "unknown")]
pub use unknown_os::init_prometheus;

pub fn register<T: Clone + Collector + 'static>(
	metric: T,
	registry: &Registry,
) -> Result<T, PrometheusError> {
	registry.register(Box::new(metric.clone()))?;
	Ok(metric)
}

// On WASM `init_prometheus` becomes a no-op.
#[cfg(target_os = "unknown")]
mod unknown_os {
	use super::*;

	pub enum Error {}

	pub async fn init_prometheus(_: SocketAddr, _registry: Registry) -> Result<(), Error> {
		Ok(())
	}
}

#[cfg(not(target_os = "unknown"))]
mod known_os {
	use super::*;
	use hyper::{
		http::StatusCode,
		server::Server,
		service::{make_service_fn, service_fn},
		Body, Request, Response,
	};

	#[derive(Debug, derive_more::Display, derive_more::From)]
	pub enum Error {
		/// Hyper internal error.
		Hyper(hyper::Error),
		/// Http request error.
		Http(hyper::http::Error),
		/// i/o error.
		Io(std::io::Error),
		#[display(fmt = "Prometheus port {} already in use.", _0)]
		PortInUse(SocketAddr),
	}

	impl std::error::Error for Error {
		fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
			match self {
				Error::Hyper(error) => Some(error),
				Error::Http(error) => Some(error),
				Error::Io(error) => Some(error),
				Error::PortInUse(_) => None,
			}
		}
	}

	async fn request_metrics(
		req: Request<Body>,
		registry: Registry,
	) -> Result<Response<Body>, Error> {
		if req.uri().path() == "/metrics" {
			let metric_families = registry.gather();
			let mut buffer = vec![];
			let encoder = TextEncoder::new();
			encoder.encode(&metric_families, &mut buffer).unwrap();

			Response::builder()
				.status(StatusCode::OK)
				.header("Content-Type", encoder.format_type())
				.body(Body::from(buffer))
				.map_err(Error::Http)
		} else {
			Response::builder()
				.status(StatusCode::NOT_FOUND)
				.body(Body::from("Not found."))
				.map_err(Error::Http)
		}
	}

	#[derive(Clone)]
	pub struct Executor;

	impl<T> hyper::rt::Executor<T> for Executor
	where
		T: Future + Send + 'static,
		T::Output: Send + 'static,
	{
		fn execute(&self, future: T) {
			async_std::task::spawn(future);
		}
	}

	/// Initializes the metrics context, and starts an HTTP server
	/// to serve metrics.
	pub async fn init_prometheus(
		prometheus_addr: SocketAddr,
		registry: Registry,
	) -> Result<(), Error> {
		let listener = async_std::net::TcpListener::bind(&prometheus_addr)
			.await
			.map_err(|_| Error::PortInUse(prometheus_addr))?;

		init_prometheus_with_listener(listener, registry).await
	}

	/// Init prometheus using the given listener.
	pub(crate) async fn init_prometheus_with_listener(
		listener: async_std::net::TcpListener,
		registry: Registry,
	) -> Result<(), Error> {
		use networking::Incoming;

		log::info!("〽️ Prometheus exporter started at {}", listener.local_addr()?);

		let service = make_service_fn(move |_| {
			let registry = registry.clone();

			async move {
				Ok::<_, hyper::Error>(service_fn(move |req: Request<Body>| {
					request_metrics(req, registry.clone())
				}))
			}
		});

		let server =
			Server::builder(Incoming(listener.incoming())).executor(Executor).serve(service);

		let result = server.await.map_err(Into::into);

		result
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use hyper::{Client, Uri};
	use std::convert::TryFrom;

	#[test]
	fn prometheus_works() {
		const METRIC_NAME: &str = "test_test_metric_name_test_test";

		let runtime = tokio::runtime::Runtime::new().expect("Creates the runtime");

		let listener = runtime
			.block_on(async_std::net::TcpListener::bind("127.0.0.1:0"))
			.expect("Creates listener");

		let local_addr = listener.local_addr().expect("Returns the local addr");

		let registry = Registry::default();
		register(
			prometheus::Counter::new(METRIC_NAME, "yeah").expect("Creates test counter"),
			&registry,
		)
		.expect("Registers the test metric");

		runtime.spawn(known_os::init_prometheus_with_listener(listener, registry));

		runtime.block_on(async {
			let client = Client::new();

			let res = client
				.get(Uri::try_from(&format!("http://{}/metrics", local_addr)).expect("Parses URI"))
				.await
				.expect("Requests metrics");

			let buf = hyper::body::to_bytes(res).await.expect("Converts body to bytes");

			let body = String::from_utf8(buf.to_vec()).expect("Converts body to String");
			assert!(body.contains(&format!("{} 0", METRIC_NAME)));
		});
	}
}
