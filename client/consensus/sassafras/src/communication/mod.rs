use std::{marker::PhantomData, sync::Arc};
use sp_runtime::traits::Block as BlockT;
use sc_network::PeerId;
use sc_network_gossip::{
	Validator as ValidatorT, ValidatorContext, GossipEngine, Network as GossipNetwork,
	ValidationResult,
};

pub use sp_consensus_sassafras::SASSAFRAS_ENGINE_ID;
pub const SASSAFRAS_PROTOCOL_NAME: &[u8] = b"/paritytech/sassafras/1";

pub struct GossipValidator<Block: BlockT> {
	_marker: PhantomData<Block>,
}

impl<Block: BlockT> ValidatorT<Block> for GossipValidator<Block> {
	fn validate(
		&self,
		context: &mut dyn ValidatorContext<Block>,
		sender: &PeerId,
		data: &[u8]
	) -> ValidationResult<Block::Hash> {
		unimplemented!()
	}
}

pub struct NetworkBridge<Block: BlockT, N> {
	service: N,
	gossip_engine: GossipEngine<Block>,
	validator: Arc<GossipValidator<Block>>,
}

impl<Block: BlockT, N> NetworkBridge<Block, N> where
	N: GossipNetwork<Block> + Clone + Send + 'static,
{
	pub fn new(service: N) -> Self {
		let validator = Arc::new(GossipValidator {
			_marker: PhantomData,
		});

		let gossip_engine = GossipEngine::new(
			service.clone(),
			SASSAFRAS_ENGINE_ID,
			SASSAFRAS_PROTOCOL_NAME,
			validator.clone(),
		);

		Self {
			service,
			gossip_engine,
			validator,
		}
	}
}
