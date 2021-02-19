use thiserror::Error;

#[allow(missing_docs)]
#[derive(Debug, Error)]
pub enum Error {
	#[error("IO Error")]
	IoError(#[from] std::io::Error),
	#[error("This telemetry instance has already been initialized!")]
	TelemetryAlreadyInitialized,
	#[error("The telemetry worker has been dropped already.")]
	TelemetryWorkerDropped,
}

#[allow(missing_docs)]
pub type Result<T> = std::result::Result<T, Error>;
