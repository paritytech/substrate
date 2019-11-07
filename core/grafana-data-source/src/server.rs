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

use serde::{Serialize, de::DeserializeOwned};
use hyper::{Body, Request, Response, header, service::service_fn, Server, Chunk};
use futures::{FutureExt, StreamExt, future::select};
use chrono::{Duration, Utc};
use futures_util::stream::TryStreamExt;
use futures_timer::Delay;
use crate::{METRICS, util, types::{Target, Query, TimeseriesData}};

#[derive(Debug, derive_more::Display)]
enum Error {
	Hyper(hyper::Error),
	Serde(serde_json::Error),
	Http(hyper::http::Error)
}

impl std::error::Error for Error {}

async fn api_response(req: Request<Body>) -> Result<Response<Body>, Error> {
	match req.uri().path() {
		"/search" => {
			map_request_to_response(req, |target: Target| {
				// Filter and return metrics relating to the target
				METRICS.read()
					.keys()
					.filter(|key| key.starts_with(&target.target))
					.cloned()
					.collect::<Vec<_>>()
			}).await
		},
		"/query" => {
			map_request_to_response(req, |query: Query| {
				let metrics = METRICS.read();

				// Return timeseries data related to the specified metrics
				query.targets.iter()
					.map(|target| {
						let datapoints = metrics.get(target.target.as_str())
							.map(|metric| {
								let from = util::find_index(&metric, query.range.from);
								let to = util::find_index(&metric, query.range.to);

								// Avoid returning more than `max_datapoints` (mostly to stop
								// the web browser from having to do a ton of work)
								util::select_points(&metric[from .. to], query.max_datapoints)
							})
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

/// Start the data source server.
pub async fn run_server(address: std::net::SocketAddr) -> Result<(), hyper::Error> {
	let service = hyper::service::make_service_fn(|_| {
		async {
			Ok::<_, Error>(service_fn(api_response))
		}
	});

	let server = Server::bind(&address)
		.serve(service)
		.boxed();

	let clean = clean_up()
		.boxed();

	select(server, clean).await;

	Ok(())
}

/// Periodically remove old metrics.
async fn clean_up() {
	let every = Duration::days(1);
	let before = Duration::weeks(1);

	loop {
		Delay::new(every.to_std().unwrap()).await;

		let oldest_allowed = (Utc::now() - before).timestamp_millis();

		let mut metrics = METRICS.write();

		for metric in metrics.values_mut() {
			// Find the index of the oldest allowed timestamp and cut out all those before it.
			let index = util::find_index(&metric, oldest_allowed);

			if index > 0 {
				*metric = metric[index..].to_vec();
			}
		}
	}
}
