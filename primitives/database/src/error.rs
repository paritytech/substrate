#[derive(Debug)]
pub struct DatabaseError(pub Box<dyn std::error::Error + Send>);

impl std::fmt::Display for DatabaseError {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}

impl std::error::Error for DatabaseError {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		None
	}
}

pub type Result<T> = std::result::Result<T, DatabaseError>;
