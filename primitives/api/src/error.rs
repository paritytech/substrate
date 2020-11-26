#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
struct Error {
    tag: &'static str,
    #[source]
    error: codec::Error,
}

impl From<(&'static str, codec::Error)> for Error {
    fn from((tag, error): (&'static str, codec::Error)) -> Self {
        Self {
            tag,
            error,
        }
    }
}
