
pub struct RoundId(i32); // TODO Something more sane

pub struct Hash([u8; 32]); // TODO use H256

pub struct Signature([u8; 64]);

pub struct PublicKey([u8; 32]);

pub struct Timestamp(u64);

pub struct Amount(u64);
