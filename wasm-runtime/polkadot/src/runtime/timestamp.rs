use primitives::Timestamp;
use storage::Storage;

pub fn timestamp() -> Timestamp {
	Storage::into(b"tim\0val")
}

pub fn set_timestamp(now: Timestamp) {
	now.store(b"tim\0val")
}
