use super::{cmd::FillCmd, *};
use log::*;
use rand::prelude::*;

impl FillCmd {
	pub fn run<B>(&self, config: Configuration) -> Result<()>
	where
		B: BlockT,
	{
		let db = setup_db::<B>(&config)?;
		info!("Filling DB. {:?}", self.db_args);

		let kvs = self.db_args.prepare_kvs();
		write_kvs(&kvs, db.clone(), COLUMN);
		Ok(())
	}
}
