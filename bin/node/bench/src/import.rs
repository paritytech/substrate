use std::borrow::Cow;

use node_testing::bench::{BenchDb, Profile, BlockType, KeyTypes};
use node_primitives::Block;
use sc_client_api::backend::Backend;
use sp_runtime::generic::BlockId;

use crate::core::{self, Path};

pub struct ImportBenchmarkDescription {
	pub profile: Profile,
	pub key_types: KeyTypes,
}

pub struct ImportBenchmark {
	profile: Profile,
	database: BenchDb,
	block: Block,
}

impl core::BenchmarkDescription for ImportBenchmarkDescription {
	fn path(&self) -> Path {

		let mut path = Path::new(&["node", "import"]);

		match self.profile {
			Profile::Wasm => path.push("wasm"),
			Profile::Native => path.push("native"),
		}

		match self.key_types {
			KeyTypes::Sr25519 => path.push("sr25519"),
			KeyTypes::Ed25519 => path.push("ed25519"),
		}

		path
	}

	fn setup(self: Box<Self>) -> Box<dyn core::Benchmark> {
		let profile = self.profile;
		let mut bench_db = BenchDb::with_key_types(100, self.key_types);
		let block = bench_db.generate_block(BlockType::RandomTransfers(100));
		Box::new(ImportBenchmark {
			database: bench_db,
			block,
			profile,
		})
	}

	fn name(&self) -> Cow<'static, str> {
		match self.profile {
			Profile::Wasm => "Import benchmark (random transfers, wasm)".into(),
			Profile::Native => "Import benchmark (random transfers, native)".into(),
		}
	}
}

impl core::Benchmark for ImportBenchmark {
	fn run(&mut self) -> std::time::Duration {
		let mut context = self.database.create_context(self.profile);

        let _ = context.client.runtime_version_at(&BlockId::Number(0))
            .expect("Failed to get runtime version")
            .spec_version;

        let start = std::time::Instant::now();
        context.import_block(self.block.clone());
        let elapsed = start.elapsed();

        log::info!(
            target: "bench-logistics",
            "imported block with {} tx, took: {:#?}",
            self.block.extrinsics.len(),
            elapsed,
        );

        log::info!(
            target: "bench-logistics",
            "usage info: {}",
            context.backend.usage_info()
                .expect("RocksDB backend always provides usage info!"),
		);

		elapsed
	}
}