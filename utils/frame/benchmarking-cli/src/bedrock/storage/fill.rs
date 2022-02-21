use log::info;
use rand::prelude::*;
use std::sync::Arc;

use sc_cli::Result;
use sc_client_api::{
	blockchain::Backend as BlockchainBackend, Backend, StorageProvider, UsageProvider,
};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT},
};

use super::cmd::FillCmd;

impl FillCmd {
	/*pub fn run<B, BA, C>(&self, client: Arc<C>) -> Result<()>
	where
		C: UsageProvider<B> + StorageProvider<B, BA>,
		B: BlockT,
		BA: Backend<B>,
		<<B as BlockT>::Header as HeaderT>::Number: Default + PartialEq,
	{
		if client.usage_info().chain.best_number != Default::default() {
			return Err("DB should be empty");
		}
		let block = BlockId::number(0);

		let elements = 1<<10;
		let min_l = 1;
		let max_l = 1<<20;
		let key_l = 32;

		let mut rng = rand::thread_rng();
		let mut total_l = 0;

		for _ in 0..elements {
			let l = rng.gen_range(min_l, max_l);
			let k = random_vec(&mut rng, key_l);
			let v = random_vec(&mut rng, l);

			info!("Inserting kv lengths {}/{}", k.len(), v.len());
			client.storage(&block, &k, &StorageKey(v));
			total_l += k.len() + v.len();
		}

		info!("Inserted {} pairs with total value size {} MB", elements, total_l);
		Ok(())
	}*/
}

// Thanks Nikolay!
fn random_vec<R: Rng>(rng: &mut R, len: usize) -> Vec<u8> {
	let mut val = vec![0u8; len];
	rng.fill_bytes(&mut val[..]);
	val
}
