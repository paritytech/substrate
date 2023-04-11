use clap::Args;

/// Parameters used to config runtime.
#[derive(Debug, Clone, Args)]
pub struct RuntimeParams {
	/// The size of the instances cache for each runtime. The values higher than 256 are ignored.
	#[arg(long, default_value_t = 8)]
	pub max_runtime_instances: usize,

	/// Maximum number of different runtimes that can be cached.
	#[arg(long, default_value_t = 2)]
	pub runtime_cache_size: u8,
}

impl RuntimeParams {
	/// Normalize the params.
	pub fn normalize(&mut self) {
		if self.max_runtime_instances > 256 {
			self.max_runtime_instances = 8;
		}
	}
}
