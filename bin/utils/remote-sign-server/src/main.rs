// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

/// Example Server of the Substrate Simple Remote Signer protocol.

use structopt::StructOpt;

use tokio::stream::StreamExt;

use sc_cli::KeystoreParams;
use sc_service::config::KeystoreConfig;
use sc_keystore::LocalKeystore;
use sc_remote_signer::{
    RemoteSignerApi,
    server::GenericRemoteSignerServer
};

use tokio;
use env_logger;

#[derive(Debug, StructOpt)]
#[structopt(
    name="substrate-remote-sign-server",
    about="keystore Server for Substrate's JSON-RPC Remote Signing Protocol"
)]
struct Opt {
    #[structopt(flatten)]
    keystore: KeystoreParams,
    /// The port to listen on
    #[structopt(long = "port", short="-p", default_value="33033")]
    port: u32,
    /// The interface to listen on
    #[structopt(long = "interface", short="-i", default_value="127.0.0.1")]
    interface: String,
    // Run in websocket-mode (instead of http)
    #[structopt(long = "websocket")]
    websocket: bool,
}

#[tokio::main]
async fn main() {
    env_logger::init();
    let opt = Opt::from_args();
    let base_path = std::env::current_dir().unwrap();
    let keystore = match opt.keystore.keystore_config(&base_path) {
        Ok((_, KeystoreConfig::Path { path, password })) => {
            LocalKeystore::open(path, password).map_err(|e| format!("{:}", e))
        },
        Err(e) => Err(format!("{:}", e)),
        Ok(_) => Err(format!("Only Local-Keystore Paramters supported")),
    }.unwrap();

    let server_addr = format!("{}:{}", opt.interface, opt.port).parse()
        .expect("Could not parse interface/port");

    let (remote_server, mut receiver) = GenericRemoteSignerServer::proxy(keystore);

    tokio::spawn(async move {
        loop {
            if receiver.next().await == None {
                break
            }
        }
    });

    if opt.websocket {
        let mut io = jsonrpc_ws_server::jsonrpc_core::IoHandler::new();
        io.extend_with(RemoteSignerApi::to_delegate(remote_server));

        let server = jsonrpc_ws_server::ServerBuilder::new(io)
            .start(&server_addr)
            .unwrap();
        let _ = tokio::task::spawn_blocking(move || {
            println!("Serving Remote Signer at ws://{:}", server_addr);
            server.wait()
        }).await;

    }  else {
        let mut io = jsonrpc_http_server::jsonrpc_core::IoHandler::new();
        io.extend_with(RemoteSignerApi::to_delegate(remote_server));

        let server = jsonrpc_http_server::ServerBuilder::new(io)
            .threads(3)
            .start_http(&server_addr)
            .unwrap();
        let _ = tokio::task::spawn_blocking(move || {
            println!("Serving Remote Signer at http://{:}", server_addr);
            server.wait()
        }).await;
    }
}