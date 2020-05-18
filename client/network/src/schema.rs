// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or 
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.
//! Include sources generated from protobuf definitions.

pub mod v1 {
	include!(concat!(env!("OUT_DIR"), "/api.v1.rs"));
	pub mod finality {
		include!(concat!(env!("OUT_DIR"), "/api.v1.finality.rs"));
	}
	pub mod light {
		include!(concat!(env!("OUT_DIR"), "/api.v1.light.rs"));
	}
}
