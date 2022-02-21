use clap::Parser;
use log::info;
use sc_cli::Result;

#[derive(Debug, PartialEq, Parser)]
pub struct ExtBaseCmd {}

impl ExtBaseCmd {
	pub fn run(&self) -> Result<()> {
		info!("hello from extrinsic cmd");
		Ok(())
	}
}
