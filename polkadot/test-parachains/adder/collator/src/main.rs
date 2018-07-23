// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Collator for polkadot

extern crate adder;
extern crate polkadot_parachain as parachain;
extern crate polkadot_primitives as primitives;
extern crate polkadot_collator as collator;
extern crate ed25519;
extern crate parking_lot;
extern crate ctrlc;
extern crate futures;

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

use adder::{HeadData as AdderHead, BlockData as AdderBody};
use ed25519::Pair;
use parachain::codec::{Encode, Decode};
use primitives::parachain::{HeadData, BlockData, Id as ParaId, Message};
use collator::{InvalidHead, ParachainContext};
use futures::sync::oneshot;
use futures::Future;
use parking_lot::Mutex;

const GENESIS: AdderHead = AdderHead {
	number: 0,
	parent_hash: [0; 32],
	post_state: [1, 27, 77, 3, 221, 140, 1, 241, 4, 145, 67, 207, 156, 76, 129, 126, 75, 22, 127, 29, 27, 131, 229, 198, 240, 241, 13, 137, 186, 30, 123, 206],
};

const GENESIS_BODY: AdderBody = AdderBody {
	state: 0,
	add: 0,
};

#[derive(Clone)]
struct AdderContext {
	db: Arc<Mutex<HashMap<AdderHead, AdderBody>>>,
}

/// The parachain context.
impl ParachainContext for AdderContext {
	fn produce_candidate<I: IntoIterator<Item=(ParaId, Message)>>(
		&self,
		last_head: HeadData,
		_ingress: I,
	) -> Result<(BlockData, HeadData), InvalidHead>
	{
		let adder_head = AdderHead::decode(&mut &last_head.0[..])
			.ok_or(InvalidHead)?;

		let mut db = self.db.lock();

		let last_body = if adder_head == GENESIS {
			GENESIS_BODY
		} else {
			db.get(&adder_head)
				.expect("All past bodies stored since this is the only collator")
				.clone()
		};

		let next_body = AdderBody {
			state: last_body.state + last_body.add,
			add: adder_head.number % 100,
		};

		let next_head = ::adder::execute(adder_head.hash(), adder_head, &next_body)
			.expect("good execution params; qed");

		let encoded_head = HeadData(next_head.encode());
		let encoded_body = BlockData(next_body.encode());

		db.insert(next_head.clone(), next_body);
		Ok((encoded_body, encoded_head))
	}
}

fn main() {
	let key = Arc::new(Pair::from_seed(&[1; 32]));
	let id: ParaId = 100.into();

	// can't use signal directly here because CtrlC takes only `Fn`.
	let (exit_send, exit) = oneshot::channel();

	let exit_send_cell = RefCell::new(Some(exit_send));
	ctrlc::CtrlC::set_handler(move || {
		if let Some(exit_send) = exit_send_cell.try_borrow_mut().expect("signal handler not reentrant; qed").take() {
			exit_send.send(()).expect("Error sending exit notification");
		}
	});

	let on_exit = exit.map_err(drop);
	let context = AdderContext {
		db: Arc::new(Mutex::new(HashMap::new())),
	};

	let args: Vec<_> = ::std::env::args().into_iter().map(Into::into).collect();
	let res = ::collator::run_collator(
		context,
		id,
		on_exit,
		key,
		args,
	);

	if let Err(e) = res {
		println!("{}", e);
	}
}
