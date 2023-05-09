use crate::OnDemandBackend;
use serde::{de::DeserializeOwned, Serialize};
use sp_core::Hasher;
use sp_externalities::Extensions;
use sp_runtime::StateVersion;
use sp_state_machine::{Backend, Ext, OverlayedChanges, StorageTransactionCache};

pub struct OnDemandExt<H: Hasher>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	/// Changed storage overlay
	overlay: OverlayedChanges,
	storage_transaction_cache:
		StorageTransactionCache<<OnDemandBackend<H> as Backend<H>>::Transaction, H>,
	/// Our on-demand backend
	backend: OnDemandBackend<H>,
	/// Extensions.
	pub extensions: Extensions,
	/// State version.
	pub state_version: StateVersion,
}

impl<H: Hasher> OnDemandExt<H>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	pub fn new(
		rpc_uri: String,
		at: Option<H::Out>,
		state_version: StateVersion,
	) -> Result<Self, &'static str> {
		let backend = OnDemandBackend::new(rpc_uri, at)?;
		Ok(OnDemandExt {
			overlay: OverlayedChanges::default(),
			extensions: Default::default(),
			backend,
			storage_transaction_cache: Default::default(),
			state_version,
		})
	}

	/// Get externalities implementation.
	pub fn ext(&mut self) -> Ext<H, OnDemandBackend<H>> {
		Ext::new(
			&mut self.overlay,
			&mut self.storage_transaction_cache,
			&self.backend,
			Some(&mut self.extensions),
		)
	}
}
