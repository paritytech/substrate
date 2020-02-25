use super::api::{http as init_http, HttpApi, HttpWorker};

pub struct HttpCapability;

impl HttpCapability {
    pub fn http(&self) -> (HttpApi, HttpWorker) {
        init_http()
    }
}