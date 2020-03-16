// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use sp_consensus_aura::sr25519::{AuthorityPair as AuraPair};
use sc_cli::{VersionInfo, RuntimeAdapter};
use node_template_runtime::{Runtime, SignedExtra, Index, Balance};
use crate::{chain_spec, service, cli::Cli};
use sp_runtime::{MultiSignature, MultiSigner, generic::Era, traits::StaticLookup};
use sp_core::sr25519;

struct Adapter;

impl RuntimeAdapter for Adapter {
	type Pair = sr25519::Pair;
	type Public =  sr25519::Public;
	type Signature = MultiSignature;
	type Runtime = Runtime;
	type Extra = SignedExtra;
	type Address = <pallet_indices::Module<Runtime> as StaticLookup>::Source;

	fn build_extra(index: Index) -> Self::Extra {
		(
			frame_system::CheckVersion::new(),
			frame_system::CheckGenesis::new(),
			frame_system::CheckEra::from(Era::Immortal),
			frame_system::CheckNonce::from(index),
			frame_system::CheckWeight::new(),
			pallet_transaction_payment::ChargeTransactionPayment::from(0),
		)
	}
}

/// Parse and run command line arguments
pub fn run(version: VersionInfo) -> sc_cli::Result<()> {
	let opt = sc_cli::from_args::<Cli>(&version);

	let mut config = sc_service::Configuration::from_version(&version);

	match opt.subcommand {
		Some(subcommand) => {
			subcommand.init(&version)?;
			subcommand.update_config(&mut config, chain_spec::load_spec, &version)?;
			subcommand.run::<Adapter, _, _, _>(
				config,
				|config: _| Ok(new_full_start!(config).0),
			)
		},
		None => {
			opt.run.init(&version)?;
			opt.run.update_config(&mut config, chain_spec::load_spec, &version)?;
			opt.run.run(
				config,
				service::new_light,
				service::new_full,
				&version,
			)
		},
	}
}
