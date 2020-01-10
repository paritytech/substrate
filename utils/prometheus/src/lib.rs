// Copyright 2019 Parity Technologies (UK) Ltd.
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


#[macro_use]
extern crate lazy_static;
use futures_util::{FutureExt,future::{Future}};
use hyper::http::StatusCode;
use hyper::Server;
use hyper::{Body, Request, Response, service::{service_fn, make_service_fn}};
pub use prometheus::{Encoder, HistogramOpts, Opts, TextEncoder};
pub use prometheus::{Histogram, IntCounter};
pub use prometheus::IntGauge as Gauge;
pub use sp_runtime::traits::SaturatedConversion;
use std::net::SocketAddr;
#[cfg(not(target_os = "unknown"))]
mod networking;

pub use lazy_static::lazy_static;

pub fn create_gauge(name: &str, description: &str) -> Gauge {
	let opts = Opts::new(name, description);
	let gauge = Gauge::with_opts(opts).expect("Creating Gauge Failed");
	prometheus::register(Box::new(gauge.clone())).expect("Registering gauge failed");
	gauge
}

#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Hyper internal error.
	Hyper(hyper::Error),
	/// Http request error.
	Http(hyper::http::Error),
	/// i/o error.
	Io(std::io::Error)
}
impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			Error::Hyper(error) => Some(error),
			Error::Http(error) => Some(error),
			Error::Io(error) => Some(error)
		}
	}
}

async fn request_metrics(req: Request<Body>) -> Result<Response<Body>, Error> {
	if req.uri().path() == "/metrics" {
		let metric_families = prometheus::gather();
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

#[cfg(not(target_os = "unknown"))]
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
#[cfg(not(target_os = "unknown"))]
pub  async fn init_prometheus(mut prometheus_addr: SocketAddr) -> Result<(), Error>{
	use async_std::{net, io};
	use networking::Incoming;
	let listener = loop {
		let listener = net::TcpListener::bind(&prometheus_addr).await;
		match listener {
			Ok(listener) => {
				log::info!("Prometheus server started at {}", prometheus_addr);
				break listener
			},
			Err(err) => match err.kind() {
				io::ErrorKind::AddrInUse | io::ErrorKind::PermissionDenied if prometheus_addr.port() != 0 => {
					log::warn!(
						"Prometheus server to already {} port.", prometheus_addr.port()
					);
					prometheus_addr.set_port(0);
					continue;
				},
				_ => return Err(err.into())
			}
		}
	};
	let service = make_service_fn(|_| {
		async {
			Ok::<_, Error>(service_fn(request_metrics))
		}
	});

	let _server = Server::builder(Incoming(listener.incoming()))
		.executor(Executor)
		.serve(service)
		.boxed();

	let result = _server.await.map_err(Into::into);

	result
}

#[cfg(target_os = "unknown")]
pub async fn init_prometheus(_: SocketAddr) -> Result<(), Error> {
	Ok(())
}
