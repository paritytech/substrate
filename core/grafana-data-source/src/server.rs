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
use hyper::{Body, Request, Response, header, service::service_fn, Server};
use futures::{future, Future, stream::Stream};
use crate::{METRICS, types::{SearchRequest, QueryRequest, TimeseriesData}};

type GenericError = Box<dyn std::error::Error + Send + Sync>;
type ResponseFuture = Box<dyn Future<Item=Response<Body>, Error=GenericError> + Send>;

fn api_response(req: Request<Body>) -> ResponseFuture {
	match req.uri().path() {
		"/" => Box::new(future::ok(Response::new(Body::empty()))),
		"/search" => map_request_to_response(req, |req: SearchRequest| {
			// Filter and return metrics relating to the search term
			METRICS.read()
				.keys()
				.filter(|key| key.starts_with(&req.target))
				.cloned()
				.collect::<Vec<_>>()
		}),
		"/query" => {
			map_request_to_response(req, |req: QueryRequest| {
				let metrics = METRICS.read();

				// Return timeseries data related to the specified metrics
				req.targets.iter()
					.map(|target| {
						let datapoints = metrics.get(target.target.as_str())
							.map(|metric| {
								let from = metric.binary_search_by_key(&req.range.from, |&(_, t)| t)
									.unwrap_or_else(|i| i);
								let to = metric.binary_search_by_key(&req.range.to, |&(_, t)| t)
									.unwrap_or_else(|i| i);

								let metric = &metric[from .. to];

								if metric.len() > req.max_datapoints {
									// Avoid returning more than `max_datapoints` (mostly to stop
									// the web browser from having to do a ton of work)
									select_points(metric, req.max_datapoints)
								} else {
									metric.to_vec()
								}
							})
							.unwrap_or_else(Vec::new);

						TimeseriesData {
							target: target.target.clone(), datapoints
						}
					})
					.collect::<Vec<_>>()
			})
		},
		_ => Box::new(future::ok(Response::new(Body::empty()))),
	}
}

fn map_request_to_response<Req, Res, T>(req: Request<Body>, transformation: T) -> ResponseFuture
	where
		Req: DeserializeOwned,
		Res: Serialize,
		T: Fn(Req) -> Res + Send + Sync + 'static
{
	Box::new(req.into_body()
		.concat2()
		.from_err()
		.and_then(move |entire_body| {
			let req = serde_json::from_slice(entire_body.as_ref())?;
			let res = transformation(req);

			let string = serde_json::to_string(&res)?;

			Response::builder()
				.header(header::CONTENT_TYPE, "application/json")
				.body(Body::from(string))
				.map_err(|e| e.into())
		})
	)
}

/// Start the data source server.
///
/// The server shuts down cleanly when `shutdown` resolves.
pub fn run_server<F>(address: &std::net::SocketAddr, shutdown: F) -> impl Future<Item=(), Error=()>
	where F: Future<Item = (), Error = ()>
{
	Server::bind(address)
		.serve(|| service_fn(api_response))
		.with_graceful_shutdown(shutdown)
		.map_err(|e| eprintln!("server error: {}", e))
}

// Evenly select `num_points` points from a slice
fn select_points<T: Copy>(slice: &[T], num_points: usize) -> Vec<T> {
	(0 .. num_points - 1)
		.map(|i| slice[i * slice.len() / (num_points - 1)])
		.chain(slice.last().cloned())
		.collect()
}

#[test]
fn test_select_points() {
	let array = [1, 2, 3, 4, 5];
	assert_eq!(select_points(&array, 2), vec![1, 5]);
	assert_eq!(select_points(&array, 3), vec![1, 3, 5]);
	assert_eq!(select_points(&array, 4), vec![1, 2, 4, 5]);
	assert_eq!(select_points(&array, 5), vec![1, 2, 3, 4, 5]);
}
