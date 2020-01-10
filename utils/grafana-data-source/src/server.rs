// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use serde::{Serialize, de::DeserializeOwned};
use hyper::{Body, Request, Response, header, service::{service_fn, make_service_fn}, Server};
use chrono::{Duration, Utc};
use futures_util::{FutureExt, TryStreamExt, future::{Future, select, Either}};
use futures_timer::Delay;
use crate::{DATABASE, Error, types::{Target, Query, TimeseriesData, Range}};

async fn api_response(req: Request<Body>) -> Result<Response<Body>, Error> {
	match req.uri().path() {
		"/search" => {
			map_request_to_response(req, |target: Target| {
				// Filter and return metrics relating to the target
				DATABASE.read()
					.keys_starting_with(&target.target)
					.collect::<Vec<_>>()
			}).await
		},
		"/query" => {
			map_request_to_response(req, |query: Query| {
				let metrics = DATABASE.read();

				let Query {
					range: Range { from, to },
					max_datapoints, ..
				} = query;

				// Return timeseries data related to the specified metrics
				query.targets.iter()
					.map(|target| {
						let datapoints = metrics.datapoints_between(&target.target, from, to, max_datapoints)
							.unwrap_or_else(Vec::new);

						TimeseriesData {
							target: target.target.clone(), datapoints
						}
					})
					.collect::<Vec<_>>()
			}).await
		},
		_ => Ok(Response::new(Body::empty())),
	}
}

async fn map_request_to_response<Req, Res, T>(req: Request<Body>, transformation: T) -> Result<Response<Body>, Error>
	where
		Req: DeserializeOwned,
		Res: Serialize,
		T: Fn(Req) -> Res + Send + Sync + 'static
{
	let body = req.into_body()
		.map_ok(|bytes| bytes.to_vec())
		.try_concat()
		.await
		.map_err(Error::Hyper)?;

	let req = serde_json::from_slice(body.as_ref()).map_err(Error::Serde)?;
	let res = transformation(req);
	let string = serde_json::to_string(&res).map_err(Error::Serde)?;

	Response::builder()
		.header(header::CONTENT_TYPE, "application/json")
		.body(Body::from(string))
		.map_err(Error::Http)
}

/// Given that we're not using hyper's tokio feature, we need to define out own executor.
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

/// Start the data source server.
#[cfg(not(target_os = "unknown"))]
pub async fn run_server(mut address: std::net::SocketAddr) -> Result<(), Error> {
	use async_std::{net, io};
	use crate::networking::Incoming;

	let listener = loop {
		let listener = net::TcpListener::bind(&address).await;
		match listener {
			Ok(listener) => {
				log::info!("Grafana data source server started at {}", address);
				break listener
			},
			Err(err) => match err.kind() {
				io::ErrorKind::AddrInUse | io::ErrorKind::PermissionDenied if address.port() != 0 => {
					log::warn!(
						"Unable to bind grafana data source server to {}. Trying random port.",
						address
					);
					address.set_port(0);
					continue;
				},
				_ => return Err(err.into()),
			}
		}
	};

	let service = make_service_fn(|_| {
		async {
			Ok::<_, Error>(service_fn(api_response))
		}
	});

	let server = Server::builder(Incoming(listener.incoming()))
		.executor(Executor)
		.serve(service)
		.boxed();

	let every = std::time::Duration::from_secs(24 * 3600);
	let clean = clean_up(every, Duration::weeks(1))
		.boxed();

	let result = match select(server, clean).await {
		Either::Left((result, _)) => result.map_err(Into::into),
		Either::Right((result, _)) => result
	};

	result
}

#[cfg(target_os = "unknown")]
pub async fn run_server(_: std::net::SocketAddr) -> Result<(), Error> {
	Ok(())
}

/// Periodically remove old metrics.
async fn clean_up(every: std::time::Duration, before: Duration) -> Result<(), Error> {
	loop {
		Delay::new(every).await;

		let oldest_allowed = (Utc::now() - before).timestamp_millis();
		DATABASE.write().truncate(oldest_allowed)?;
	}
}
