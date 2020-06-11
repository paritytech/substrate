#[derive(Debug)]
pub struct DatabaseError(pub Box<dyn std::error::Error>);

impl std::fmt::Display for DatabaseError {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{:?}", self)
	}
}

pub type Result<T> = std::result::Result<T, DatabaseError>;
