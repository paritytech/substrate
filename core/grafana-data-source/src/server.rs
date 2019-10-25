use serde::{Serialize, de::DeserializeOwned};
use hyper::{Body, Request, Response, header, service::service_fn, Server};
use futures::{future, Future, stream::Stream};
use crate::{METRICS, types::{SearchRequest, QueryRequest, TimeseriesData}};

type GenericError = Box<dyn std::error::Error + Send + Sync>;
type ResponseFuture = Box<dyn Future<Item=Response<Body>, Error=GenericError> + Send>;

fn api_response(req: Request<Body>) -> ResponseFuture {
	match req.uri().path() {
		"/" => Box::new(future::ok(Response::new(Body::empty()))),
		"/search" => respond(req, |_: SearchRequest| METRICS.read().keys().cloned().collect::<Vec<_>>()),
		"/query" => {
			respond(req, |req: QueryRequest| {
				let metrics = METRICS.read();

				req.targets.iter()
					.map(|target| {
						let datapoints = metrics.get(&target.target).iter()
							.flat_map(|&vec| vec)
							.filter(|(_, timestamp)| req.range.from <= *timestamp && *timestamp <= req.range.to)
							.map(|(value, timestamp)| (*value, timestamp.timestamp_millis() as u64))
							.collect();

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

fn respond<Req, Res, T>(req: Request<Body>, transformation: T) -> ResponseFuture
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

pub fn run_server(address: &std::net::SocketAddr) -> impl Future<Item=(), Error=()> {
	Server::bind(address)
		.serve(|| service_fn(api_response))
		.map_err(|e| eprintln!("server error: {}", e))
}
