// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
	dispatch::{CallMetadata, DispatchInfo, PostDispatchInfo},
	traits::{GetCallMetadata, UnfilteredDispatchable},
};
use codec::{Decode, Encode};
use sp_core::H256;
use sp_runtime::{
	traits, traits::Dispatchable, DispatchError, DispatchResultWithInfo, ModuleError,
	MAX_MODULE_ERROR_ENCODED_SIZE,
};
sp_api::decl_runtime_apis! {
	pub trait Interface<View>
		where View: sp_api::Decode + View
	{

		// TOOD: Macro does not handle that well
		//fn view(view: Self::View) -> Result<Vec<u8>, Error>;
		fn view(view: View) -> InterfaceViewResult;
	}
}

pub type InterfaceResult = Result<(), Error>;
pub type InterfaceViewResult = Result<Vec<u8>, Error>;
pub type InterfaceResultWithPostInfo = InterfaceErrorWithPostInfo<PostDispatchInfo>;

#[derive(
	Eq,
	PartialEq,
	Clone,
	Copy,
	Encode,
	Decode,
	frame_support::RuntimeDebug,
	frame_support::scale_info::TypeInfo,
)]
pub struct InterfaceErrorWithPostInfo<Info>
where
	Info: Eq + PartialEq + Clone + Copy + Encode + Decode + traits::Printable,
{
	pub post_info: Info,
	pub error: Error,
}

impl From<Error> for InterfaceErrorWithPostInfo<PostDispatchInfo> {
	fn from(error: Error) -> Self {
		InterfaceErrorWithPostInfo { post_info: PostDispatchInfo::default(), error }
	}
}

pub trait Core {
	type RuntimeOrigin;
	type Selectable: From<H256> + Into<H256>;
}

pub trait Call {
	type RuntimeOrigin;
	type Selectable: From<H256> + Into<H256>;

	fn call(
		self,
		origin: Self::RuntimeOrigin,
		selectable: Self::Selectable,
	) -> InterfaceResultWithPostInfo;
}

pub trait View {
	type Selectable: From<H256> + Into<H256>;

	fn view(self) -> Result<Vec<u8>, Error>;
}

pub trait Selector {
	type Selectable;
	type Selected;

	fn select(&self, selectable: Self::Selectable) -> Result<Self::Selected, Error>;
}

/// The "high-level" error enum of interfaces
///
/// Amalgamates all inner interfaces errors
#[derive(
	Eq,
	PartialEq,
	Clone,
	Copy,
	Encode,
	Decode,
	frame_support::RuntimeDebug,
	frame_support::scale_info::TypeInfo,
)]
pub enum Error {
	SelectorMismatch { provided: H256 },
	Interface(InterfaceError),
	Module(ModuleError),
}

/// Reason why a pallet call failed.
#[derive(Eq, Clone, Copy, Encode, Decode, Debug, TypeInfo, MaxEncodedLen)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct InterfaceError {
	/// Module index, matching the metadata module index.
	pub index: u8,
	/// Module specific error value.
	pub error: [u8; MAX_MODULE_ERROR_ENCODED_SIZE],
	/// Optional error message.
	#[codec(skip)]
	#[cfg_attr(feature = "std", serde(skip_deserializing))]
	pub message: Option<&'static str>,
}

impl From<ModuleError> for Error {
	fn from(m: ModuleError) -> Self {
		Self::Module(m)
	}
}

impl From<InterfaceError> for Error {
	fn from(m: InterfaceError) -> Self {
		Self::Interface(m)
	}
}

// THis is then used in the uper level logic
impl From<Error> for DispatchError {
	fn from(value: Error) -> Self {
		todo!()
	}
}

pub struct EmptySelector;

impl EmptySelector {
	pub fn new() -> Self {
		EmptySelector {}
	}
}

impl Selector for EmptySelector {
	type Selectable = H256;
	type Selected = ();

	fn select(&self, from: Self::Selectable) -> Result<Self::Selected, Error> {
		match from {
			x if x == H256::zero() => Ok(()),
			_ => Err(Error::SelectorMismatch { provided: from }),
		}
	}
}

pub struct Select<T> {
	from: H256,
	selector: Box<dyn Selector<Selected = T, Selectable = H256>>,
}

impl<T> Select<T> {
	pub fn new(from: H256, selector: Box<dyn Selector<Selected = T, Selectable = H256>>) -> Self {
		Select { from, selector }
	}

	pub fn select(&self) -> Result<T, Error> {
		self.selector.as_ref().select(self.from)
	}
}

mod tests {
	#[frame_support::interface]
	mod int_123 {
		use frame_support::{
			dispatch::DispatchResult,
			interface::{Error, InterfaceResult, InterfaceResultWithPostInfo, Select},
			Parameter,
		};

		#[interface::definition]
		#[interface::with_selector]
		pub trait Pip20: frame_support::interface::Core {
			type AccountId: Parameter;
			type Currency: Parameter;
			type Balance: Parameter;

			#[interface::selector(SelectCurrency)]
			#[interface::default_selector]
			fn select_currency(selectable: Self::Selectable) -> Result<Self::Currency, Error>;

			#[interface::selector(RestrictedCurrency)]
			fn select_restricted_currency(
				selectable: Self::Selectable,
			) -> Result<Self::Currency, Error>;

			#[interface::selector(SelectAccount)]
			fn select_account(selectable: Self::Selectable) -> Result<Self::AccountId, Error>;

			#[interface::view]
			#[interface::view_index(0)]
			fn free_balance(
				currency: Select<Self::Currency>,
				who: Self::AccountId,
			) -> Result<Self::Balance, Error>;

			#[interface::view]
			#[interface::view_index(1)]
			#[interface::no_selector]
			fn balances(
				who: Self::AccountId,
			) -> Result<Vec<(Self::Currency, Self::Balance)>, Error>;

			#[interface::call]
			#[interface::call_index(0)]
			#[interface::weight(0)]
			fn transfer(
				origin: Self::RuntimeOrigin,
				currency: Select<Self::Currency>,
				recv: Self::AccountId,
				amount: Self::Balance,
			) -> InterfaceResultWithPostInfo;

			#[interface::call]
			#[interface::call_index(3)]
			#[interface::weight(0)]
			#[interface::no_selector]
			fn burn(
				origin: Self::RuntimeOrigin,
				from: Self::AccountId,
				amount: Self::Balance,
			) -> InterfaceResult;

			#[interface::call]
			#[interface::call_index(1)]
			#[interface::use_selector(RestrictedCurrency)]
			#[interface::weight(0)]
			fn approve(
				origin: Self::RuntimeOrigin,
				currency: Select<Self::Currency>,
				recv: Self::AccountId,
				amount: Self::Balance,
			) -> InterfaceResult;
		}
	}
}

/*
#[frame_support::call_interface]
pub enum CallInterface {
	#[call_index(20)]
	Pip20(pip20::Call<Runtime>, pip20::Event, pip20::Error),
}

construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
		Interface = Interface<CallInterface<Self>, H256>,
	{
		System: frame_system,
	}
);

pub mod __expanded {
	use super::*;
	use crate::dispatch::{DispatchResultWithPostInfo, GetCallName, GetDispatchInfo};

	pub enum Call {
		System(frame_system::Call) = 0,
		Interface(Interface<CallInterface, H256>) = 255,
	}

	pub struct Interface<CallInterface: Call<RuntimeOrigin = RuntimeOrigin>, Selectable> {
		selectable: Selectable,
		interface: CallInterface,
	}

	impl<CallInterface, Selectable> UnfilteredDispatchable for Interface<CallInterface, Selectable> {
		type RuntimeOrigin = RuntimeOrigin;

		fn dispatch_bypass_filter(self, origin: Self::RuntimeOrigin) -> DispatchResultWithPostInfo {
			match self.interface {
				CallInterface::Pip20(call) => call.call(origin, self.selectable.into()),
			}
		}
	}

	impl<Runtime> GetDispatchInfo for CallInterface<Runtime> {
		fn get_dispatch_info(&self) -> DispatchInfo {
			todo!()
		}
	}

	impl<Runtime> GetCallName for CallInterface<Runtime> {
		fn get_call_names() -> &'static [&'static str] {
			todo!()
		}

		fn get_call_name(&self) -> &'static str {
			todo!()
		}
	}
}

#[frame_support::view_interface]
pub enum ViewInterface<Runtime> {
	#[call_index(20)]
	Pip20(pip20::View<Runtime, pip20::Selector>),
}

pub mod __expandend_view {
	use super::*;
	impl<Runtime> View for ViewInterface<Runtime> {
		fn view(&self) -> Vec<u8> {
			match self {
				ViewInterface::Pip20(view) => view.view(),
			}
		}
	}
}

pub mod pip721 {
	#[frame_support::interface]
	#[interface::extend(Pip20(Call, View, Error, Event))]
	pub trait Pip721: frame_support::interface::Core {
		type AccountId;
		type Collection;
		type Item;

		#[interface::view]
		fn holdings(who: Self::AccountId) -> Vec<(Self::Collection, Self::Item)>;

		#[interface::call]
		fn vanish(
			origin: Self::RuntimeOrigin,
			recv: Self::AccountId,
			collection: Self::Collection,
			item: Self::Item,
			cost: u32,
		) -> DispatchResult;
	}

	pub mod __expanded {
		pub trait Pip721 {
			type AccountId;
			type Collection;
			type Item;

			fn holdings(who: Self::AccountId) -> Vec<(Self::Collection, Self::Item)>;

			fn vanish(
				origin: Self::RuntimeOrigin,
				recv: Self::AccountId,
				collection: Self::Collection,
				item: Self::Item,
				cost: u32,
			) -> DispatchResult;
		}

		pub enum View<Runtime: Pip721 + Core> {
			Holdings { who: Runtime::AccountId } = 0,
		}

		impl<Runtime: Pip721 + Core> View for View<Runtime> {
			type Selectable = <Runtime as Core>::Selectable;

			fn view(&self) -> Result<Vec<u8>, Error> {
				match self {
					View::Holdings { who } => Ok(<Runtime as Pip721>::holdings(who).encode()),
				}
			}
		}

		pub enum Call<Runtime: Pip721 + Core> {
			Vanish {
				recv: <Runtime as Pip721>::AccountId,
				collection: <Runtime as Pip721>::Collection,
				item: <Runtime as Pip721>::Item,
				cost: u32,
			} = 0,
		}

		impl<Runtime: Pip721 + Core> super::Call for Call<Runtime> {
			type RuntimeOrigin = <Runtime as Core>::RuntimeOrigin;
			type Selectable = <Runtime as Core>::Runtime::Selectable;

			fn call(
				self,
				origin: Self::RuntimeOrigin,
				selectable: Self::Selectable,
			) -> DispatchResultWithPostInfo {
				match self {
					Vanish { recv, collection, item, cost } =>
						<Runtime as Pip721>::approve(origin, collection, item, cost),
				}
			}
		}
	}
}

pub mod pip20 {
	#[frame_support::interface]
	#[interface::with_selector]
	pub trait Pip20 {
		type AccountId;
		type Currency;
		type Balance;

		#[interface::selector(SelectCurrency)]
		#[interface::default_selector]
		fn select_currency(selectable: Self::Selectable) -> Result<Self::Currency, Error>;

		#[interface::selector(RestrictedCurrency)]
		fn select_restricted_currency(selectable:  Self::Selectable) -> Result<Self::Currency, Error>;

		#[interface::selector(SelectAccount)]
		fn select_account(selectable:  Self::Selectable) -> Result<Self::Account, Error>;

		#[interface::view]
		#[interface::view_index(0)]
		fn free_balance(currency: Select<Self::Currency>, who: Self::AccountId) -> Self::Balance;

		#[interface::view]
		#[interface::view_index(1)]
		#[interface::no_selector]
		fn balances(who: Self::AccountId) -> Vec<(Self::Currency, Self::Balance)>;

		#[interface::call]
		#[interface::call_index(0)]
		fn transfer(
			origin: Self::RuntimeOrigin,
			currency: Select<Self::Currency>,
			recv: Self::AccountId,
			amount: Self::Balance,
		) -> DispatchResult;

		#[interface::call]
		#[interface::call_index(1)]
		#[interface::use_selector(RestrictedCurrency)]
		fn approve(
			origin: Self::RuntimeOrigin,
			currency: Select<Self::Currency>,
			recv: Self::AccountId,
			amount: Self::Balance,
		) -> DispatchResult;

		#[interface::call]
		#[interface::call_index(3)]
		#[interface::use_selector(SelectAccount)]
		fn burn(
			origin: Self::RuntimeOrigin,
			from: Select<Self::AccountId>,
			amount: Self::Balance,
		) -> DispatchResult;
	}

	pub mod __expanded {
		pub trait Pip20: Core {
			type AccountId;
			type Currency;
			type Balance;

			fn select_currency(selectable: H256) -> Result<Self::Currency, Error>;

			fn select_restricted_currency(selectable: H256) -> Result<Self::Currency, Error>;

			fn select_account(selectable: H256) -> Result<Self::Account, Error>;

			fn free_balance(
				currency: Select<Self::Currency>,
				who: Self::AccountId,
			) -> Self::Balance;

			fn balances(who: Self::AccountId) -> Vec<(Self::Currency, Self::Balance)>;

			fn transfer(
				origin: Self::RuntimeOrigin,
				currency: Select<Self::Currency>,
				recv: Self::AccountId,
				amount: Self::Balance,
			) -> DispatchResult;

			fn approve(
				origin: Self::RuntimeOrigin,
				currency: Select<Self::Currency>,
				recv: Self::AccountId,
				amount: Self::Balance,
			) -> DispatchResult;

			fn burn(
				origin: Self::RuntimeOrigin,
				from: Select<Self::AccountId>,
				amount: Self::Balance,
			) -> DispatchResult;
		}

		pub struct SelectCurrency<Runtime>;
		impl<Runtime: Pip20 + Core> Selector for SelectCurrency<Runtime> {
			type Selected = <Runtime as Pip20>::Currency;
			type Selectable = <Runtime as Core>::Selectable;

			fn select(&self, from: Self::Selectable) -> Result<Self::Selected, Error> {
				<Runtime as Pip20>::select_currency(from)
			}
		}

		pub struct SelectRestrictedCurrency<Runtime>;
		impl<Runtime: Pip20 + Core> Selector for SelectRestrictedCurrency<Runtime> {
			type Selected = <Runtime as Pip20>::Currency;

			fn select(&self, from: H256) -> Result<Self::Selected, Error> {
				<Runtime as Pip20>::select_restricted_currency(from)
			}
		}

		pub struct SelectAccount<Runtime>;
		impl<Runtime: Pip20 + Core> Selector for SelectAccount<Runtime> {
			type Selected = <Runtime as Pip20>::AccountId;

			fn select(&self, from: H256) -> Result<Self::Selected, Error> {
				<Runtime as Pip20>::select_account(from)
			}
		}

		pub enum View<Runtime: Pip20 + Core> {
			FreeBalance { who: Runtime::AccountId } = 0,
			Balances { who: Runtime::AccountId } = 1,
		}

		impl<Runtime: Pip20 + Core> View for View<Runtime> {
			type Selectable = <Runtime as Core>::Selectable;

			fn view(&self, selectable: Self::Selectable) -> Result<Vec<u8>, Error> {
				match self {
					View::FreeBalance { who } => {
						let select = Select::new(selector, Box::new(SelectCurrency::<Runtime> {}));
						Ok(<Runtime as Pip20>::free_balance(select, who).encode())
					},
					View::Balances { who } => Ok(<Runtime as Pip20>::balances(who).encode()),
				}
			}
		}

		pub enum Call<Runtime: Pip20 + Core> {
			Transfer { recv: Runtime::AccountId, amount: Runtime::Balance } = 0,
			Approve { recv: Runtime::AccountId, amount: Runtime::Balance } = 1,
			Burn { amount: Runtime::Balance } = 3,
		}

		impl<Runtime: Pip20 + Core> super::Call for Call<Runtime> {
			type RuntimeOrigin = <Runtime as Core>::RuntimeOrigin;
			type Selectable = <Runtime as Core>::Runtime::Selectable;

			fn call(
				self,
				origin: Self::RuntimeOrigin,
				selectable: Self::Selectable,
			) -> DispatchResultWithPostInfo {
				match self {
					Call::Transfer { recv, amount } => {
						let select = Select::new(selector, Box::new(SelectCurrency::<Runtime> {}));
						<Runtime as Pip20>::transfer(origin, select, recv, amount)
					},
					Call::Approve { recv, amount } => {
						let select =
							Select::new(selector, Box::new(SelectRestrictedCurrency::<Runtime> {}));
						<Runtime as Pip20>::approve(origin, select, recv, amount)
					},
					Call::Burn { amount } => {
						let select = Select::new(selector, Box::new(SelectAccount::<Runtime> {}));
						<Runtime as Pip20>::burn(origin, select, amount)
					},
				}
			}
		}
	}
}

#[frame_support::interface]
#[interface::extends(Pip1(Call, View)), Pip2(Call)]
mod interface {
	#[interface::definition]
	pub trait Pip20: frame_support::interface::Core {}

	#[interface::error]
	pub enum Error {}

	#[interface::error]
	pub enum Event {}
}
 */
