#![allow(unused)] // TODO

pub mod benches;
pub mod command;

use clap::{ArgEnum, Parser};
use sc_cli::{DatabaseParams, SharedParams};

#[derive(Debug, Parser)]
pub struct BedrockCmd {
	#[clap(long = "type", arg_enum)]
	pub bedrock_type: BedrockType,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub bedrock_params: BedrockParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub database_params: DatabaseParams,
}

// TODO make PascalCase
#[derive(Debug, Copy, Clone, PartialEq, Eq, ArgEnum)]
#[clap(rename_all = "SnakeCase")]
pub enum BedrockType {
	BlockImport,
	DbRead,
	DbWrite,
	TxExecution,
}

#[derive(Debug, Parser)]
pub struct BedrockParams {
	//#[clap(long)]
//pub repeat: u32,
}
