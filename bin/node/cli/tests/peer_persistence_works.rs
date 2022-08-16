use assert_cmd::cargo::cargo_bin;
use sc_network::{
	config::identity::{ed25519, Keypair},
	PeerId,
};
use std::{path::PathBuf, process::Command};
use tempfile::tempdir;

pub mod common;

#[tokio::test]
#[cfg(unix)]
async fn purge_chain_works() {
	const NODES_COUNT: usize = 10;

	const IDX_GROUP_FIRST: usize = 0;
	const IDX_GROUP_LAST: usize = NODES_COUNT - 3;
	const IDX_POS: usize = NODES_COUNT - 1;
	const IDX_NEG: usize = NODES_COUNT - 2;

	let mut node_defs = (0..NODES_COUNT)
		.map(|idx| {
			let node_key = ed25519::SecretKey::generate();
			let node_identity = Keypair::Ed25519(ed25519::Keypair::from(node_key.to_owned()))
				.public()
				.to_peer_id();
			NodeDef {
				var_run_dir: tempdir().expect("could not create a temp dir").into_path(),
				node_key,
				node_identity,
				p2p_port: p2p_port(idx),
				ws_port: ws_port(idx),
				rpc_port: rpc_port(idx),
				validator_name: None,
				bootnodes: vec![],
				disable_peers_persistence: false,
				running: None,
			}
		})
		.collect::<Vec<_>>();

	let bootnode = node_defs[0].boot_addr();
	node_defs.iter_mut().skip(1).for_each(|def| {
		def.bootnodes = vec![bootnode.to_owned()];
	});

	node_defs[0].validator_name = Some("--alice");
	node_defs[1].validator_name = Some("--bob");
	node_defs[2].validator_name = Some("--charlie");

	// node_defs[IDX_POS].bootnodes = vec![node_defs[IDX_ALT_BOOT].boot_addr()];
	// node_defs[IDX_NEG].bootnodes = vec![node_defs[IDX_ALT_BOOT].boot_addr()];
	node_defs[IDX_NEG].disable_peers_persistence = true;

	for idx in IDX_GROUP_FIRST..=IDX_GROUP_LAST {
		node_defs[idx].start();
	}

	tokio::time::sleep(std::time::Duration::from_secs(30)).await;
	assert!(wait_n_blocks_if_spawned(3, 30, &node_defs[..]).await);

	node_defs[IDX_POS].start();
	node_defs[IDX_NEG].start();

	tokio::time::sleep(std::time::Duration::from_secs(30)).await;
	assert!(wait_n_blocks_if_spawned(3, 30, &node_defs[..]).await);

	node_defs[IDX_POS].stop();
	node_defs[IDX_NEG].stop();

	node_defs[IDX_POS].bootnodes = vec![];
	node_defs[IDX_NEG].bootnodes = vec![];
	node_defs[IDX_POS].p2p_port += 3;
	node_defs[IDX_NEG].p2p_port += 3;
	node_defs[IDX_POS].start();
	node_defs[IDX_NEG].start();
	tokio::time::sleep(std::time::Duration::from_secs(30)).await;

	assert!(wait_n_blocks_if_spawned(3, 30, &node_defs[IDX_GROUP_FIRST..=IDX_GROUP_LAST],).await);
	assert!(wait_n_blocks_if_spawned(3, 30, std::iter::once(&node_defs[IDX_POS])).await);
	assert!(!wait_n_blocks_if_spawned(3, 30, std::iter::once(&node_defs[IDX_NEG])).await);
}

async fn wait_n_blocks_if_spawned<'a, 'b>(
	n_blocks: usize,
	within_secs: u64,
	node_defs: impl IntoIterator<Item = &'b NodeDef<'a>>,
) -> bool
where
	'a: 'b,
{
	let nodes_queried = node_defs.into_iter().map(|node| {
		let ws_url = node.ws_url();
		let is_spawned = node.running.is_some();

		async move {
			if is_spawned {
				common::wait_n_finalized_blocks(n_blocks, within_secs, &ws_url).await.is_ok()
			} else {
				true
			}
		}
	});

	futures::future::join_all(nodes_queried)
		.await
		.into_iter()
		.all(std::convert::identity)
}

struct NodeDef<'a> {
	var_run_dir: PathBuf,
	node_key: ed25519::SecretKey,
	node_identity: PeerId,
	p2p_port: u16,
	ws_port: u16,
	rpc_port: u16,
	validator_name: Option<&'a str>,
	bootnodes: Vec<String>,
	disable_peers_persistence: bool,
	running: Option<common::KillChildOnDrop>,
}

impl NodeDef<'_> {
	pub fn start(&mut self) {
		assert!(self.running.is_none());

		let child = self.command().spawn().expect("Failed to spawn OS-Process");
		let child = common::KillChildOnDrop(child);
		self.running = Some(child);
	}
	pub fn stop(&mut self) {
		assert!(self.running.is_some());
		self.running = None;
	}

	pub fn ws_url(&self) -> String {
		format!("ws://127.0.0.1:{}", self.ws_port)
	}
	pub fn boot_addr(&self) -> String {
		format!("/ip4/127.0.0.1/tcp/{}/p2p/{}", self.p2p_port, self.node_identity)
	}

	fn command(&self) -> Command {
		let base_path = {
			let mut p = self.var_run_dir.to_owned();
			p.push(format!("node-{}.d", self.node_identity));
			p
		};

		let mut cmd = Command::new(cargo_bin("substrate"));
		cmd.args(&["--base-path", base_path.as_os_str().to_str().unwrap()]);
		cmd.args(&["--no-mdns"]);
		cmd.args(&["--chain", "local"]);
		cmd.args(&["--port", &self.p2p_port.to_string()]);
		cmd.args(&["--ws-port", &self.ws_port.to_string()]);
		cmd.args(&["--rpc-port", &self.rpc_port.to_string()]);
		cmd.args(&["--node-key", &hex::encode(&self.node_key)]);

		if let Some(name) = self.validator_name {
			cmd.args(&[name]);
		}
		for bootnode in self.bootnodes.iter() {
			cmd.args(&["--bootnodes", bootnode.as_str()]);
		}
		if self.disable_peers_persistence {
			cmd.args(&["--disable-peers-persistence"]);
		}

		eprintln!("CMD: {:#?}", cmd);

		cmd
	}
}

fn p2p_port(node_id: usize) -> u16 {
	(35000 + node_id * 10) as u16
}
fn ws_port(node_id: usize) -> u16 {
	(35000 + node_id * 10 + 1) as u16
}
fn rpc_port(node_id: usize) -> u16 {
	(35000 + node_id * 10 + 2) as u16
}
