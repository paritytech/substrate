use clap::Parser;
use log::info;
use sc_cli::{CliConfiguration, DatabaseParams, PruningParams, Result, SharedParams};

#[derive(Debug, PartialEq, Parser)]
pub struct DbWriteCmd {}

impl DbWriteCmd {
	pub fn run(&self) -> Result<()> {
		info!("hello from db write cmd");
		Ok(())
	}
}
