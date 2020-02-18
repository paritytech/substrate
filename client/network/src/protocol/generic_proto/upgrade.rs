// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

pub use self::collec::UpgradeCollec;
pub use self::legacy::{
	RegisteredProtocol,
	RegisteredProtocolEvent,
	RegisteredProtocolName,
	RegisteredProtocolSubstream
};
pub use self::notifications::{
	NotificationsIn,
	NotificationsInSubstream,
	NotificationsOut,
	NotificationsOutSubstream,
	NotificationsHandshakeError,
	NotificationsOutError,
};

mod collec;
mod legacy;
mod notifications;
