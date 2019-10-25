use serde::{Serialize, Deserialize, de::DeserializeOwned};
use hyper::{Body, Request, Response, header, service::service_fn, Server};
use futures::{future, Future, stream::Stream};
use chrono::{DateTime, Utc, Duration};
use rand::{thread_rng, Rng};

type GenericError = Box<dyn std::error::Error + Send + Sync>;
type ResponseFuture = Box<dyn Future<Item=Response<Body>, Error=GenericError> + Send>;

#[derive(Serialize, Deserialize, Debug)]
enum TargetType {
    #[serde(rename = "timeseries")]
    Timeseries,
    #[serde(rename = "table")]
    Table
}

#[derive(Serialize, Deserialize)]
pub struct SearchRequest {
    target: String
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct QueryRequest {
    interval_ms: u64,
    max_data_points: u64,
    targets: Vec<Target>,
    range: Range,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct Target {
    target: Metric,
    #[serde(rename = "type")]
    target_type: TargetType,
}

#[derive(Serialize, Deserialize, Debug)]
struct Range {
    from: DateTime<Utc>,
    to: DateTime<Utc>,
}

#[derive(Serialize, Deserialize, Debug)]
struct TimeseriesData {
    target: Metric,
    datapoints: Vec<(f32, u64)>
}

#[derive(Serialize, Deserialize, Debug, Copy, Clone)]
enum Metric {
    #[serde(rename = "a")]
    A,
    #[serde(rename = "ab")]
    Ab,
    #[serde(rename = "abc")]
    Abc
}

fn api_response(req: Request<Body>) -> ResponseFuture {
    match req.uri().path() {
        "/" => Box::new(future::ok(Response::new(Body::empty()))),
        "/search" => {
            respond(req, |_: SearchRequest| {
                [Metric::A, Metric::Ab, Metric::Abc]
            })
        },
        "/query" => {
            respond(req, |req: QueryRequest| {
                req.targets.iter()
                    .map(|target| {
                        // Create some bogus data points
                        let datapoints = (0 .. 1000)
                            .map(|i| (
                                thread_rng().gen_range(0.0, 10_000.0),
                                (Utc::now() - Duration::days(i))
                            ))
                            .filter(|(_, timestamp)| timestamp >= &req.range.from && timestamp <= &req.range.to)
                            .map(|(i, datetime)| (i, datetime.timestamp_millis() as u64))
                            .collect();

                        TimeseriesData {
                            target: target.target, datapoints
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