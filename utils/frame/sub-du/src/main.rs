use ansi_term::{Colour::*, Style};
use frame_metadata::{RuntimeMetadata, RuntimeMetadataPrefixed, StorageEntryType};
use remote_externalities::{twox_128, StorageKey};
use sc_rpc_api::state::StateApiClient;
use separator::Separatable;
use sp_runtime::testing::{Block as RawBlock, ExtrinsicWrapper, H256 as Hash};
use structopt::StructOpt;

const KB: usize = 1024;
const MB: usize = KB * KB;
const GB: usize = MB * MB;

pub const LOG_TARGET: &'static str = "sub-du";

fn get_prefix(indent: usize) -> &'static str {
	match indent {
		1 => "├─┬",
		2 => "│ │─┬",
		3 => "│ │ │─",
		_ => panic!("Unexpected indent."),
	}
}

struct Size(usize);

impl std::fmt::Display for Size {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if self.0 <= KB {
			write!(f, "{: <4}B", self.0)?;
		} else if self.0 <= MB {
			write!(f, "{: <4}K", self.0 / KB)?;
		} else if self.0 <= GB {
			write!(f, "{: <4}M", self.0 / MB)?;
		}

		Ok(())
	}
}

#[derive(Debug, Clone, Default)]
struct Pallet {
	pub name: String,
	pub size: usize,
	pub items: Vec<Storage>,
}

impl std::fmt::Display for Pallet {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let mod_style = Style::new().bold().italic().fg(Green);
		write!(
			f,
			"{} {} {}\n",
			mod_style.paint(format!("{}", Size(self.size))),
			get_prefix(2),
			mod_style.paint(self.name.clone())
		)?;
		for s in self.items.iter() {
			write!(f, "{} {} {}\n", Size(s.size), get_prefix(3), s)?;
		}
		Ok(())
	}
}

impl Pallet {
	fn new(name: String) -> Self {
		Self { name, ..Default::default() }
	}
}

#[derive(Debug, Copy, Clone)]
pub enum StorageItem {
	Value(usize),
	Map(usize, usize),
}

impl std::fmt::Display for StorageItem {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Value(bytes) => write!(f, "Value({} bytes)", bytes.separated_string()),
			Self::Map(bytes, count) => {
				write!(f, "Map({} bytes, {} keys)", bytes.separated_string(), count)
			},
		}
	}
}

impl Default for StorageItem {
	fn default() -> Self {
		Self::Value(0)
	}
}

#[derive(Debug, Clone, Default)]
struct Storage {
	pub name: String,
	pub size: usize,
	pub item: StorageItem,
}

impl std::fmt::Display for Storage {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let item_style = Style::new().italic();
		write!(f, "{} => {}", item_style.paint(self.name.clone()), self.item)
	}
}

impl Storage {
	fn new(name: String, item: StorageItem) -> Self {
		let size = match item {
			StorageItem::Value(s) => s,
			StorageItem::Map(s, _) => s,
		};
		Self { name, item, size }
	}
}

#[derive(Debug, StructOpt)]
#[structopt(
	name = "sub-du",
	about = "a du-like tool that prints the map of storage usage of a substrate chain"
)]
struct Opt {
	/// The block number at which the scrap should happen. Use only the hex value, no need for a
	/// `0x` prefix.
	#[structopt(long)]
	at: Option<Hash>,

	/// The node to connect to.
	#[structopt(long, default_value = "ws://localhost:9944")]
	uri: String,

	/// If true, intermediate values will be printed.
	#[structopt(long, short)]
	progress: bool,

	/// Weather to scrape all pairs or just the size of them.
	///
	/// If enabled, the command might take longer but then the number of keys in each map is also
	/// scraped.
	///
	/// # Warning
	///
	/// This uses an unsafe RPC call and can only be used if the target node allows it.
	#[structopt(long, short)]
	scrape_pairs: bool,
}

/// create key prefix for a module as vec bytes. Basically twox128 hash of the given values.
pub fn pallet_prefix_raw(module: &[u8], storage: &[u8]) -> Vec<u8> {
	let module_key = twox_128(module);
	let storage_key = twox_128(storage);
	let mut final_key = Vec::with_capacity(module_key.len() + storage_key.len());
	final_key.extend_from_slice(&module_key);
	final_key.extend_from_slice(&storage_key);
	final_key
}

type Block = RawBlock<ExtrinsicWrapper<Hash>>;

#[async_std::main]
async fn main() -> () {
	let opt = Opt::from_args();

	// connect to a node.
	let ext = remote_externalities::Builder::<Block>::new();
	let mut modules: Vec<Pallet> = vec![];

	// potentially replace head with the given hash
	let head = ext.rpc_get_head().await.unwrap();
	let at = opt.at.or(Some(head));

	let rpc_client = ext.as_online().rpc_client();

	let runtime = rpc_client.runtime_version(at).await.unwrap();

	println!("Scraping at block {:?} of {}({})", at, runtime.spec_name, runtime.spec_version,);

	let raw_metadata = rpc_client.metadata(at).await.unwrap();
	let prefixed_metadata = <RuntimeMetadataPrefixed as codec::Decode>::decode(&mut &*raw_metadata)
		.expect("Runtime Metadata failed to decode");
	let metadata = prefixed_metadata.1;

	if let RuntimeMetadata::V14(inner) = metadata {
		let pallets = inner.pallets;
		for pallet in pallets.into_iter() {
			let name = pallet.name;

			// skip, if this module has no storage items.
			if pallet.storage.is_none() {
				log::warn!(
					target: LOG_TARGET,
					"Pallet with name {:?} seems to have no storage items.",
					name
				);
				continue
			}

			let storage = pallet.storage.unwrap();
			let prefix = storage.prefix;
			let entries = storage.entries;
			let mut pallet_info = Pallet::new(name.clone());

			for storage_entry in entries.into_iter() {
				let storage_name = storage_entry.name;
				let ty = storage_entry.ty;
				let key_prefix = pallet_prefix_raw(prefix.as_bytes(), storage_name.as_bytes());

				let (pairs, size) = if opt.scrape_pairs {
					// this should be slower but gives more detail.
					let pairs =
						rpc_client.storage_pairs(StorageKey(key_prefix.clone()), at).await.unwrap();
					let pairs = pairs
						.into_iter()
						.map(|(k, v)| (k.0, v.0))
						.collect::<Vec<(Vec<u8>, Vec<u8>)>>();
					let size = pairs.iter().fold(0, |acc, x| acc + x.1.len());
					(pairs, size)
				} else {
					// This should be faster
					let size = rpc_client
						.storage_size(StorageKey(key_prefix), at)
						.await
						.unwrap()
						.unwrap_or_default() as usize;
					let pairs: Vec<_> = vec![];
					(pairs, size)
				};

				log::debug!(
					target: LOG_TARGET,
					"{:?}::{:?} => count: {}, size: {} bytes",
					name,
					storage_name,
					pairs.len(),
					size
				);

				pallet_info.size += size;
				let item = match ty {
					StorageEntryType::Plain(_) => StorageItem::Value(size),
					StorageEntryType::Map { .. } => StorageItem::Map(size, pairs.len()),
				};
				pallet_info.items.push(Storage::new(storage_name, item));
			}
			pallet_info.items.sort_by_key(|x| x.size);
			pallet_info.items.reverse();
			println!("Scraped module {}. Total size {}.", pallet_info.name, pallet_info.size,);
			if opt.progress {
				print!("{}", pallet_info);
			}
			modules.push(pallet_info);
		}

		println!("Scraping results done. Final sorted tree:");
		modules.sort_by_key(|m| m.size);
		modules.reverse();

		let total: usize = modules.iter().map(|m| m.size).sum();
		println!("{} {} {}", Size(total), get_prefix(1), runtime.spec_name,);
		modules.into_iter().for_each(|m| {
			print!("{}", m);
		});
	} else {
		panic!("Unsupported Metadata version");
	}
}
