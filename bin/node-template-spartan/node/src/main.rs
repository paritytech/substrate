//! Substrate Node Template CLI library.
//! Forked from https://github.com/substrate-developer-hub/substrate-node-template/
#![warn(missing_docs)]

mod chain_spec;
#[macro_use]
mod service;
mod cli;
mod command;
mod rpc;

fn main() -> sc_cli::Result<()> {
    command::run()
}
