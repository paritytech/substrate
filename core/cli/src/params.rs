// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "Substrate")]
/// CLI Parameters provided by default
pub struct CoreParams {
    ///Sets a custom logging filter
    #[structopt(short = "l", long = "log", value_name = "LOG_PATTERN")]
    log: Option<String>,

    #[structopt(long = "base-path", short = "d", value_name = "PATH", parse(from_os_str))]
    /// Specify custom base path
    base_path: Option<PathBuf>,

    #[structopt(long = "keystore-path", value_name = "PATH", parse(from_os_str))]
    /// Specify custom keystore path
    keystore_path: Option<PathBuf>,

    #[structopt(long = "key", value_name = "STRING")]
    /// Specify additional key seed
    key: Option<String>,

    #[structopt(long = "node-key", value_name = "KEY")]
    /// Specify node secret key (64-character hex string)
    node_key: Option<String>,
    
    #[structopt(long = "validator")]
    /// Enable validator mode
    validator: bool,

    #[structopt(long = "light")]
    /// Run in light client mode
    light: bool,
  
    #[structopt(long = "dev")]
    /// Run in development mode; implies --chain=dev --validator --key Alice
    dev: bool,
  
    #[structopt(long = "listen-addr", value_name = "LISTEN_ADDR")]
    /// Listen on this multiaddress
    listen_addr: Vec<String>,
  
    #[structopt(long = "port", value_name = "PORT")]
    /// Specify p2p protocol TCP port. Only used if --listen-addr is not specified.
    port: Option<u32>,
  
    #[structopt(long = "rpc-external")]
    /// Listen to all RPC interfaces (default is local)
    rpc_external: bool,
  
    #[structopt(long = "ws-external")]
    /// Listen to all Websocket interfaces (default is local)
    ws_external: bool,
  
    #[structopt(long = "rpc-port", value_name = "PORT")]
    /// Specify HTTP RPC server TCP port
    rpc_port: Option<u32>,
  
    #[structopt(long = "ws-port", value_name = "PORT")]
    /// Specify WebSockets RPC server TCP port
    ws_port: Option<u32>,
  
    #[structopt(long = "bootnodes", value_name = "URL")]
    /// Specify a list of bootnodes
    bootnodes: Vec<String>,
  
    #[structopt(long = "reserved-nodes", value_name = "URL")]
    /// Specify a list of reserved node addresses
    reserved_nodes: Vec<String>,
  
    #[structopt(long = "out-peers", value_name = "OUT_PEERS")]
    /// Specify the number of outgoing connections we're trying to maintain
    out_peers: Option<u8>,
  
    #[structopt(long = "in-peers", value_name = "IN_PEERS")]
    /// Specify the maximum number of incoming connections we're accepting
    in_peers: Option<u8>,
  
    #[structopt(long = "chain", value_name = "CHAIN_SPEC")]
    /// Specify the chain specification (one of dev, local or staging)
    chain: Option<String>,
  
    #[structopt(long = "pruning", value_name = "PRUNING_MODE")]
    /// Specify the pruning mode, a number of blocks to keep or 'archive'. Default is 256.
    pruning: Option<u32>,
  
    #[structopt(long = "name", value_name = "NAME")]
    /// The human-readable name for this node, as reported to the telemetry server, if enabled
    name: Option<String>,
  
    #[structopt(short = "t", long = "telemetry")]
    /// Should connect to the Substrate telemetry server (telemetry is off by default on local chains)
    telemetry: bool,
  
    #[structopt(long = "no-telemetry")]
    /// Should not connect to the Substrate telemetry server (telemetry is on by default on global chains)
    no_telemetry: bool,
  
    #[structopt(long = "telemetry-url", value_name = "TELEMETRY_URL")]
    /// The URL of the telemetry server. Implies --telemetry
    telemetry_url: Option<String>,

    #[structopt(long = "execution", value_name = "STRATEGY")]
    /// The means of execution used when calling into the runtime. Can be either wasm, native or both.
    execution: Option<ExecutionStrategy>,

    #[structopt(subcommand)]
    cmds: Option<CoreCommands>,
}

/// How to execute blocks
#[derive(Debug, StructOpt)]
pub enum ExecutionStrategy {
    /// Execute native only
    Native,
    /// Execute wasm only
    Wasm,
    /// Execute natively when possible, wasm otherwise
    Both,
}

impl Default for ExecutionStrategy {
    fn default() -> Self {
        ExecutionStrategy::Both
    }
}

impl std::str::FromStr for ExecutionStrategy {
    type Err = String;
    fn from_str(input: &str) -> Result<Self, Self::Err> {
        match input {
            "native" => Ok(ExecutionStrategy::Native),
            "wasm" | "webassembly" => Ok(ExecutionStrategy::Wasm),
            "both" => Ok(ExecutionStrategy::Both),
            _ => Err("Please specify either 'native', 'wasm' or 'both".to_owned())

        }
    }
}

/// Subcommands provided by Default
#[derive(Debug, StructOpt)]
pub enum CoreCommands {
    #[structopt(name = "build-spec")]
    /// Build a spec.json file, outputing to stdout
    BuildSpec {
        #[structopt(long = "raw")]
        /// Force raw genesis storage output.
        raw: bool,
        
        #[structopt(long = "chain", value_name = "CHAIN_SPEC")]
        /// Specify the chain specification (one of dev, local or staging)
        chain: Option<String>,
        
        #[structopt(long = "dev")]
        /// Specify the development chain
        dev: bool,
    },

    #[structopt(name = "export-blocks")]
    /// Export blocks to a file
    ExportBlocks {
        #[structopt(parse(from_os_str))]
        /// Output file name or stdout if unspecified.
        output: Option<PathBuf>,
        
        #[structopt(long = "chain", value_name = "CHAIN_SPEC")]
        /// Specify the chain specification.
        chain: Option<String>,
        
        #[structopt(long = "dev")]
        /// Specify the development chain
        dev: bool,
        
        #[structopt(long = "base-path", short = "d", value_name = "PATH")]
        /// Specify custom base path.
        base_path: Option<String>,
        
        #[structopt(long = "from", value_name = "BLOCK")]
        /// Specify starting block number. 1 by default.
        from: Option<u128>,
        
        #[structopt(long = "to", value_name = "BLOCK")]
        /// Specify last block number. Best block by default.
        to: Option<u128>,
        
        #[structopt(long = "json")]
        /// Use JSON output rather than binary.
        json: bool,
    },

    #[structopt(name = "import-blocks")]
    /// Import blocks from file.
    ImportBlocks {
        #[structopt(parse(from_os_str))]
        /// Input file or stdin if unspecified.
        input: Option<PathBuf>,
        
        #[structopt(long = "chain", value_name = "CHAIN_SPEC")]
        /// Specify the chain specification.
        chain: Option<String>,
          
        #[structopt(long = "dev")]
        /// Specify the development chain
        dev: bool,
        
        #[structopt(long = "base-path", short = "d", value_name = "PATH", parse(from_os_str))]
        /// Specify custom base path.
        base_path: Option<PathBuf>,
        
        #[structopt(long = "execution", value_name = "STRATEGY")]
        /// The means of execution used when executing blocks. Can be either wasm, native or both.
        execution: ExecutionStrategy,
        
        #[structopt(long = "api-execution", value_name = "STRATEGY")]
        /// The means of execution used when calling into the runtime. Can be either wasm, native or both.
        api_execution: ExecutionStrategy,
        
        #[structopt(long = "max-heap-pages", value_name = "COUNT")]
        /// The maximum number of 64KB pages to ever allocate for Wasm execution. Don't alter this unless you know what you're doing.
        max_heap_pages: Option<u32>,
    },

    #[structopt(name = "revert")]
    ///Revert chain to the previous state
    Revert {
        /// Number of blocks to revert. Default is 256.
        num: Option<u32>,
        
        #[structopt(long = "chain", value_name = "CHAIN_SPEC")]
        /// Specify the chain specification.
        chain: Option<String>,
        
        #[structopt(long = "dev")]
        /// Specify the development chain
        dev: bool,
        
        #[structopt(long = "base-path", short = "d", value_name = "PATH", parse(from_os_str))]
        /// Specify custom base path.
        base_path: Option<PathBuf>,
    },

    /// Remove the whole chain data.
    #[structopt(name = "purge-chain")]
    PurgeChain {
        /// Specify the chain specification.
        #[structopt(long = "chain", value_name = "CHAIN_SPEC")]
        chain: Option<String>,
        
        /// Specify the development chain
        #[structopt(long = "dev")]
        dev: bool,
        
        /// Specify custom base path.
        #[structopt(long = "base-path", short = "d", value_name = "PATH", parse(from_os_str))]
        base_path: Option<PathBuf>
    }
}
