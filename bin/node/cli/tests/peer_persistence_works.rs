use assert_cmd::cargo::cargo_bin;
use futures::future;
use sc_network::{
	config::identity::{ed25519, Keypair},
	PeerId,
};
use std::{path::PathBuf, process::Command};
use tempfile::tempdir;

pub mod common;

#[tokio::test]
async fn peer_persistence_works() {
	// Start a series of nodes.
	const NODES_COUNT: usize = 10;
	// The first of them will be validators.
	const VALIDATORS: &[&str] = &["--alice", "--bob", "--charlie"];

	// The "positive case" node: the peers are persisted.
	const IDX_POS: usize = NODES_COUNT - 1;
	// The "negative case" node: the peers are not persisted.
	const IDX_NEG: usize = NODES_COUNT - 2;

	// The bootnode used for everyone except that very boot-node, and the postiive- and
	// negative-case nodes.
	const IDX_PRIMARY_BOOT_NODE: usize = 0; // Alice

	// The bootnode used for the postivie- and negative-case nodes.
	const IDX_SECONDARY_BOOT_NODE: usize = 2; // Charlie

	// Define the nodes' start arguments.
	let mut node_defs = (0..NODES_COUNT)
		.map(|idx| {
			let node_key = ed25519::SecretKey::generate();
			let node_identity = Keypair::Ed25519(ed25519::Keypair::from(node_key.to_owned()))
				.public()
				.to_peer_id();
			Node {
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

	// The negative-case node does not persist peers.
	node_defs[IDX_NEG].disable_peers_persistence = true;

	let bootnodes_primary = vec![node_defs[IDX_PRIMARY_BOOT_NODE].boot_addr()];
	let bootnodes_secondary = vec![node_defs[IDX_SECONDARY_BOOT_NODE].boot_addr()];

	// Set the bootnodes:
	// - the primary bootnode does not need a bootnode;
	// - the negative- and positive-case nodes use the secondary bootnode;
	// - the rest of the nodes use the primary bootnode.
	node_defs.iter_mut().enumerate().for_each(|(idx, node)| {
		node.bootnodes = match idx {
			IDX_PRIMARY_BOOT_NODE => vec![],
			IDX_NEG | IDX_POS => bootnodes_secondary.to_owned(),
			_ => bootnodes_primary.to_owned(),
		}
	});

	// Set the validator args
	for (idx, validator_key_arg) in VALIDATORS.into_iter().copied().enumerate() {
		node_defs[idx].validator_name = Some(validator_key_arg);
	}

	// Start all the nodes except the negative- and positive-case nodes.
	node_defs.iter_mut().enumerate().for_each(|(idx, node)| match idx {
		IDX_POS | IDX_NEG => (),
		_ => node.start(),
	});

	// Ensure that all the started nodes keep finalizing blocks.
	assert!(wait_n_blocks_if_running(3, 60, &node_defs[..]).await);

	// Start the positive- and negative-case nodes.
	node_defs[IDX_POS].start();
	node_defs[IDX_NEG].start();

	// Ensure that all the started nodes keep finalizing blocks.
	assert!(wait_n_blocks_if_running(3, 60, &node_defs[..]).await);

	// Terminate the secondary bootnode.
	node_defs[IDX_SECONDARY_BOOT_NODE].stop();

	// Stop the positive- and negative-case nodes.
	node_defs[IDX_POS].stop();
	node_defs[IDX_NEG].stop();

	// Change the positive- and negative-case nodes' ports, so that the remaining nodes won't drag
	// them back into the network.
	node_defs[IDX_POS].p2p_port += 3;
	node_defs[IDX_NEG].p2p_port += 3;
	// Start the positive- and negative-case nodes.
	node_defs[IDX_POS].start();
	node_defs[IDX_NEG].start();

	// Expected:
	// - positive-case node successfully catches up with the network;
	// - negative-case node does not get updates on the finalized nodes;
	// - the rest of the started nodes keep working.
	let pos_queried = wait_n_blocks_if_running(3, 60, std::iter::once(&node_defs[IDX_POS]));
	let neg_queried = wait_n_blocks_if_running(3, 60, std::iter::once(&node_defs[IDX_NEG]));
	let the_rest_queried = wait_n_blocks_if_running(
		3,
		60,
		node_defs.iter().enumerate().filter_map(|(idx, node)| match idx {
			IDX_POS | IDX_NEG => None,
			_ => Some(node),
		}),
	);
	assert_eq!(
		future::join(future::join(pos_queried, neg_queried), the_rest_queried).await,
		((true, false), true)
	);
}

async fn wait_n_blocks_if_running<'a, 'b>(
	n_blocks: usize,
	within_secs: u64,
	node_defs: impl IntoIterator<Item = &'b Node<'a>>,
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

	future::join_all(nodes_queried).await.into_iter().all(std::convert::identity)
}

struct Node<'a> {
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

impl Node<'_> {
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
