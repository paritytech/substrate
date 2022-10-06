//! Some helper functions for common substrate chains.

use crate::{Hash, Client};
use ansi_term::Colour;
use codec::{Decode, Encode};
use frame_support::{Blake2_128Concat, Twox64Concat};
use frame_system::AccountInfo;
use pallet_balances::AccountData;
use std::fmt::Debug;

/// Get the nick of a given account id.
pub async fn get_nick<Balance: Decode>(who: &[u8], client: &Client, at: Hash) -> String {
	let nick = crate::read::<(Vec<u8>, Balance)>(
		crate::map_key::<Twox64Concat>(b"Nicks", b"NameOf", who.as_ref()),
		client,
		at,
	)
	.await;

	if nick.is_some() {
		String::from_utf8(nick.unwrap().0).unwrap()
	} else {
		String::from("[NO_NICK]")
	}
}

/// Get the identity of an account.
pub async fn get_identity<
	AccountId: Decode + AsRef<[u8]>,
	Balance: Encode + Decode + Copy + Clone + Debug + Eq + PartialEq,
>(
	who: &[u8],
	client: &Client,
	at: Hash,
) -> String {
	use pallet_identity::{Data, Registration};

	let maybe_subidentity = crate::read::<(AccountId, Data)>(
		crate::map_key::<Blake2_128Concat>(b"Identity", b"SuperOf", who.as_ref()),
		client,
		at,
	)
	.await;

	let maybe_identity = crate::read::<Registration<Balance>>(
		crate::map_key::<Twox64Concat>(
			b"Identity",
			b"IdentityOf",
			maybe_subidentity.as_ref().map_or(who.as_ref(), |x| x.0.as_ref()),
		),
		client,
		at,
	)
	.await;

	if let Some(identity) = maybe_identity {
		let info = identity.info;
		let display = info.display;

		let result = match display {
			Data::Raw(bytes) => format!(
				"{}",
				Colour::Yellow.bold().paint(String::from_utf8(bytes).expect("Identity not utf-8"))
			),
			_ => format!("{}", Colour::Red.bold().paint("???")),
		};
		if let Some(sub_identity) = maybe_subidentity {
			match sub_identity.1 {
				Data::Raw(bytes) => format!(
					"{} ({})",
					result,
					Colour::Yellow.paint(String::from_utf8(bytes).expect("Identity not utf-8"))
				),
				_ => format!("{}", Colour::Red.paint("???")),
			}
		} else {
			result
		}
	} else {
		"NO_IDENT".to_string()
	}
}

/// Get the account data at the given block.
pub async fn get_account_data_at<Balance: Decode, Nonce: Decode>(
	account: &[u8],
	client: &Client,
	at: Hash,
) -> AccountInfo<Nonce, AccountData<Balance>> {
	crate::read::<AccountInfo<Nonce, AccountData<Balance>>>(
		crate::map_key::<Blake2_128Concat>(b"System", b"Account", account.as_ref()),
		client,
		at,
	)
	.await
	.unwrap()
}
