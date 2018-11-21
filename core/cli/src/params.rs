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
pub struct CoreParams {
    #[structopt(short = "l", long = "log", value_name = "LOG_PATTERN", help = "Sets a custom logging filter")]
    log: Option<String>,

    #[structopt(long = "base-path", short = "d", value_name = "PATH", help = "Specify custom base path", parse(from_os_str))]
    base_path: Option<PathBuf>,

    #[structopt(long = "keystore-path", value_name = "PATH", help = "Specify custom keystore path", parse(from_os_str))]
    keystore_path: Option<PathBuf>,

    #[structopt(long = "key", value_name = "STRING", help = "Specify additional key seed")]
    key: Option<String>,

    #[structopt(long = "node-key", value_name = "KEY", help = "Specify node secret key (64-character hex string)")]
    node_key: Option<String>,
    
    #[structopt(long = "validator",help = "Enable validator mode")]
    validator: bool,

    #[structopt(long = "light", help = "Run in light client mode")]
    light: bool,
  
    #[structopt(long = "dev", help = "Run in development mode; implies --chain=dev --validator --key Alice")]
    dev: bool,
  
    #[structopt(long = "listen-addr", value_name = "LISTEN_ADDR", help = "Listen on this multiaddress")]
    listen_addr: Vec<String>,
  
    #[structopt(long = "port", value_name = "PORT", help = "Specify p2p protocol TCP port. Only used if --listen-addr is not specified.")]
    port: Option<u32>,
  
    #[structopt(long = "rpc-external", help = "Listen to all RPC interfaces (default is local)")]
    rpc_external: bool,
  
    #[structopt(long = "ws-external", help = "Listen to all Websocket interfaces (default is local)")]
    ws_external: bool,
  
    #[structopt(long = "rpc-port", value_name = "PORT", help = "Specify HTTP RPC server TCP port")]
    rpc_port: Option<u32>,
  
    #[structopt(long = "ws-port", value_name = "PORT", help = "Specify WebSockets RPC server TCP port")]
    ws_port: Option<u32>,
  
    #[structopt(long = "bootnodes", value_name = "URL", help = "Specify a list of bootnodes")]
    bootnodes: Vec<String>,
  
    #[structopt(long = "reserved-nodes", value_name = "URL", help = "Specify a list of reserved node addresses")]
    reserved_nodes: Vec<String>,
  
    #[structopt(long = "out-peers", value_name = "OUT_PEERS", help = "Specify the number of outgoing connections we're trying to maintain")]
    out_peers: Option<u8>,
  
    #[structopt(long = "in-peers", value_name = "IN_PEERS", help = "Specify the maximum number of incoming connections we're accepting")]
    in_peers: Option<u8>,
  
    #[structopt(long = "chain", value_name = "CHAIN_SPEC", help = "Specify the chain specification (one of dev, local or staging)")]
    chain: Option<String>,
  
    #[structopt(long = "pruning", value_name = "PRUNING_MODE", help = "Specify the pruning mode, a number of blocks to keep or 'archive'. Default is 256.")]
    pruning: Option<u32>,
  
    #[structopt(long = "name", value_name = "NAME", help = "The human-readable name for this node, as reported to the telemetry server, if enabled")]
    name: Option<String>,
  
    #[structopt(short = "t", long = "telemetry", help = "Should connect to the Substrate telemetry server (telemetry is off by default on local chains)")]
    telemetry: bool,
  
    #[structopt(long = "no-telemetry", help = "Should not connect to the Substrate telemetry server (telemetry is on by default on global chains)")]
    no_telemetry: bool,
  
    #[structopt(long = "telemetry-url", value_name = "TELEMETRY_URL", help = "The URL of the telemetry server. Implies --telemetry")]
    telemetry_url: Option<String>,

    #[structopt(long = "execution", value_name = "STRATEGY", help = "The means of execution used when calling into the runtime. Can be either wasm, native or both.")]
    execution: Option<ExecutionStrategy>,

    #[structopt(subcommand)]
    cmds: Option<CoreCommands>,
}

#[derive(Debug, StructOpt)]
pub enum ExecutionStrategy {
    Native,
    Wasm,
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

#[derive(Debug, StructOpt)]
pub enum CoreCommands {
    #[structopt(name = "build-spec", about = "Build a spec.json file, outputing to stdout")]
    BuildSpec {
        #[structopt(long = "raw", help = "Force raw genesis storage output.")]  
        raw: bool,
        
        #[structopt(long = "chain", value_name = "CHAIN_SPEC", help = "Specify the chain specification (one of dev, local or staging)")]
        chain: Option<String>,
        
        #[structopt(long = "dev", help = "Specify the development chain")]
        dev: bool,
    },

    #[structopt(name = "export-blocks", about = "Export blocks to a file")]
    ExportBlocks {
        #[structopt(help = "Output file name or stdout if unspecified.", parse(from_os_str))]    
        OUTPUT: Option<PathBuf>,
        
        #[structopt(long = "chain", value_name = "CHAIN_SPEC", help = "Specify the chain specification.")]
        chain: Option<String>,
        
        #[structopt(long = "dev", help = "Specify the development chain")]
        dev: bool,
        
        #[structopt(long = "base-path", short = "d", value_name = "PATH", help = "Specify custom base path.")]
        base_path: Option<String>,
        
        #[structopt(long = "from", value_name = "BLOCK", help = "Specify starting block number. 1 by default.")]
        from: Option<u128>,
        
        #[structopt(long = "to", value_name = "BLOCK", help = "Specify last block number. Best block by default.")]
        to: Option<u128>,
        
        #[structopt(long = "json", help = "Use JSON output rather than binary.")]
        json: bool,
    },

    #[structopt(name = "import-blocks", about = "Import blocks from file.")]
    ImportBlocks {
        #[structopt(help = "Input file or stdin if unspecified.", parse(from_os_str))]    
        INPUT: Option<PathBuf>,
        
        #[structopt(long = "chain", value_name = "CHAIN_SPEC", help = "Specify the chain specification.")]
        chain: Option<String>,
          
        #[structopt(long = "dev", help = "Specify the development chain")]
        dev: bool,
        
        #[structopt(long = "base-path", short = "d", value_name = "PATH", help = "Specify custom base path.", parse(from_os_str))]
        base_path: Option<PathBuf>,
        
        #[structopt(long = "execution", value_name = "STRATEGY", help = "The means of execution used when executing blocks. Can be either wasm, native or both.")]
        execution: ExecutionStrategy,
        
        #[structopt(long = "api-execution", value_name = "STRATEGY", help = "The means of execution used when calling into the runtime. Can be either wasm, native or both.")]
        api_execution: ExecutionStrategy,
        
        #[structopt(long = "max-heap-pages", value_name = "COUNT", help = "The maximum number of 64KB pages to ever allocate for Wasm execution. Don't alter this unless you know what you're doing.")]
        max_heap_pages: Option<u32>,
    },

    #[structopt(name = "revert", about = "Revert chain to the previous state")]
    Revert {
        #[structopt(help = "Number of blocks to revert. Default is 256.")]    
        NUM: Option<u32>,
        
        #[structopt(long = "chain", value_name = "CHAIN_SPEC", help = "Specify the chain specification.")]
        chain: Option<String>,
        
        #[structopt(long = "dev", help = "Specify the development chain")]
        dev: bool,
        
        #[structopt(long = "base-path", short = "d", value_name = "PATH", help = "Specify custom base path.", parse(from_os_str))]
        base_path: Option<PathBuf>,
    },

    #[structopt(name = "purge-chain", about = "Remove the whole chain data.")]
    PurgeChain {
        #[structopt(long = "chain", value_name = "CHAIN_SPEC", help = "Specify the chain specification.")]    
        chain: Option<String>,
        
        #[structopt(long = "dev", help = "Specify the development chain")]
        dev: bool,
        
        #[structopt(long = "base-path", short = "d", value_name = "PATH", help = "Specify custom base path.", parse(from_os_str))]
        base_path: Option<PathBuf>
    }
}
