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
	dispatch::{CallMetadata, DispatchInfo, DispatchResultWithPostInfo, PostDispatchInfo},
	traits::{EnqueueMessage, GetCallMetadata, UnfilteredDispatchable},
};
use codec::{Decode, Encode};
use frame_support::dispatch::DispatchErrorWithPostInfo;
use sp_core::H256;
use sp_runtime::{
	traits,
	traits::{Dispatchable, Zero},
	DispatchError, DispatchResultWithInfo, InterfaceError, ModuleError,
	MAX_MODULE_ERROR_ENCODED_SIZE,
};

/// Runtime API that provides view access
sp_api::decl_runtime_apis! {
	pub trait Interface<View>
		where View: sp_api::Encode + frame_support::interface::View
	{
		fn view(view: frame_support::interface::InterfaceViewEntry<View>) -> ViewResult<Vec<u8>>;
	}
}

/// The result a call method of an interface must have
pub type CallResult = Result<PostDispatchInfo, DispatchErrorWithPostInfo>;

/// The result a view method of an interface must have
pub type ViewResult<T> = Result<T, DispatchErrorWithPostInfo>;

/// The result a selector method of an interface must have
pub type SelectorResult<T> = Result<SelectorResultWithInfo<T>, DispatchErrorWithPostInfo>;

/// A helper struct that provides easy conversions
///
/// I.e. it allows somebody who does not care about
///      the `PostDispatchInfo` in a selector method
///      to just call `Ok(T.into())` instead of
///      Ok((T, ().into())) if we used a tuple.
pub struct SelectorResultWithInfo<T> {
	res: T,
	info: PostDispatchInfo,
}

impl<T> From<T> for SelectorResultWithInfo<T> {
	fn from(value: T) -> Self {
		SelectorResultWithInfo { res: value, info: Default::default() }
	}
}

impl<T> From<(T, PostDispatchInfo)> for SelectorResultWithInfo<T> {
	fn from(value: (T, PostDispatchInfo)) -> Self {
		SelectorResultWithInfo { res: value.0, info: value.1 }
	}
}

impl<T> SelectorResultWithInfo<T> {
	/// Consumes self and returns the
	/// inner T
	pub fn result(self) -> T {
		self.res
	}

	/// Provides a copy of the inner
	/// `PostDispatchInfo`
	pub fn info(&self) -> PostDispatchInfo {
		self.info
	}

	/// Destructs self into a tuple of `(T, PostDispatchInfo)`
	pub fn destruct(self) -> (T, PostDispatchInfo) {
		(self.res, self.info)
	}
}

pub trait Core: 'static + Eq + Clone {
	type RuntimeOrigin;
}

pub trait Call {
	type RuntimeOrigin;

	fn call(self, origin: Self::RuntimeOrigin, selectable: H256) -> CallResult;
}

pub trait View {
	fn view(self, selectable: H256) -> ViewResult<Vec<u8>>;
}

pub trait Selector {
	type Selected;

	fn select(&self, selectable: H256) -> SelectorResult<Self::Selected>;
}

#[derive(
	PartialEq, Eq, Clone, Copy, Encode, Decode, Debug, scale_info::TypeInfo, codec::MaxEncodedLen,
)]
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
pub struct InterfaceCallEntry<CallInterface> {
	selectable: H256,
	interface: CallInterface,
}

impl<CallInterface> UnfilteredDispatchable for InterfaceCallEntry<CallInterface>
where
	CallInterface: Call<RuntimeOrigin = <CallInterface as Core>::RuntimeOrigin> + Core,
{
	type RuntimeOrigin = <CallInterface as Core>::RuntimeOrigin;

	fn dispatch_bypass_filter(self, origin: Self::RuntimeOrigin) -> DispatchResultWithPostInfo {
		self.interface.call(origin, self.selectable)
	}
}

#[derive(
	PartialEq, Eq, Clone, Copy, Encode, Decode, Debug, scale_info::TypeInfo, codec::MaxEncodedLen,
)]
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
pub struct InterfaceViewEntry<ViewInterface> {
	selectable: H256,
	interface: ViewInterface,
}

impl<ViewInterface> InterfaceViewEntry<ViewInterface>
where
	ViewInterface: View,
{
	pub fn view(self) -> ViewResult<Vec<u8>> {
		self.interface.view(self.selectable)
	}
}

pub struct EmptySelector;

impl EmptySelector {
	pub fn new() -> Self {
		EmptySelector {}
	}
}

impl Selector for EmptySelector {
	type Selected = ();

	fn select(&self, from: H256) -> SelectorResult<Self::Selected> {
		match from {
			x if x == H256::zero() => Ok(().into()),
			_ => Err(InterfaceError::ExpectedEmptySelectable.into()),
		}
	}
}

pub struct Select<T> {
	from: H256,
	selector: Box<dyn Selector<Selected = T>>,
}

impl<T> Select<T> {
	pub fn new(from: H256, selector: Box<dyn Selector<Selected = T>>) -> Self {
		Select { from, selector }
	}

	pub fn select(self) -> SelectorResult<T> {
		self.selector.as_ref().select(self.from)
	}
}

mod tests {
	#[frame_support::interface]
	mod int_123 {
		use crate::interface::{CallResult, ViewResult};
		use frame_support::{
			dispatch::DispatchResult,
			interface::{Select, SelectorResult},
			Parameter,
		};
		use sp_core::H256;
		use sp_runtime::traits::Member;

		#[interface::definition]
		#[interface::with_selector]
		pub trait Pip20: frame_support::interface::Core {
			type AccountId: Parameter + Member;
			type Currency: Parameter + Member;
			type Balance: Parameter + Member;

			#[interface::selector(SelectCurrency)]
			#[interface::default_selector]
			fn select_currency(selectable: H256) -> SelectorResult<Self::Currency>;

			#[interface::selector(RestrictedCurrency)]
			fn select_restricted_currency(selectable: H256) -> SelectorResult<Self::Currency>;

			#[interface::selector(SelectAccount)]
			fn select_account(selectable: H256) -> SelectorResult<Self::AccountId>;

			#[interface::selector(SelectOrigin)]
			fn select_origin(
				selectable: H256,
			) -> SelectorResult<<Self as frame_support::interface::Core>::RuntimeOrigin>;

			#[interface::view]
			#[interface::view_index(0)]
			fn free_balance(
				currency: Select<Self::Currency>,
				who: Self::AccountId,
			) -> ViewResult<Self::Currency>;

			#[interface::view]
			#[interface::view_index(1)]
			#[interface::no_selector]
			fn balances(who: Self::AccountId) -> ViewResult<Vec<(Self::Currency, Self::Balance)>>;

			#[interface::call]
			#[interface::call_index(0)]
			#[interface::weight(0)]
			fn transfer(
				origin: Self::RuntimeOrigin,
				currency: Select<Self::Currency>,
				recv: Self::AccountId,
				amount: Self::Balance,
			) -> CallResult;

			#[interface::call]
			#[interface::call_index(3)]
			#[interface::weight(0)]
			#[interface::no_selector]
			fn burn(
				origin: Self::RuntimeOrigin,
				from: Self::AccountId,
				amount: Self::Balance,
			) -> CallResult;

			#[interface::call]
			#[interface::call_index(1)]
			#[interface::use_selector(RestrictedCurrency)]
			#[interface::weight(0)]
			fn approve(
				origin: Self::RuntimeOrigin,
				currency: Select<Self::Currency>,
				recv: Self::AccountId,
				amount: Self::Balance,
			) -> CallResult;
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
