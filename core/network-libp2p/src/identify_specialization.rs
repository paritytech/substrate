// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Specializations of the substrate network identify.

use libp2p::identify::protocol::IdentifyInfo;
use libp2p::PeerId;

/// A specialization of the substrate network identify.
pub trait IdentifySpecialization: Send + Sync + 'static{
	/// Get the protocol version.
	fn customize_protocol_version(&self, protocol_version: &str) -> String;
	/// Get the user agent.
	fn customize_user_agent(&self, user_agent: &str) -> String;
	/// Indicate whether should add discovered node
	fn should_add_discovered_node(&self, peer_id: &PeerId, identify_info: Option<&IdentifyInfo>) -> bool;
	/// Indicate whether should accept identify_info
	fn should_accept_identify_info(&self, peer_id: &PeerId, identify_info: &IdentifyInfo) -> bool;
}

pub struct DefaultIdentifySpecialization;

impl IdentifySpecialization for DefaultIdentifySpecialization{

	fn customize_protocol_version(&self, protocol_version: &str) -> String{

		protocol_version.to_string()
	}

	fn customize_user_agent(&self, user_agent: &str) -> String{

		user_agent.to_string()
	}

	fn should_add_discovered_node(&self, peer_id: &PeerId, identify_info: Option<&IdentifyInfo>) -> bool{
		true
	}

	fn should_accept_identify_info(&self, peer_id: &PeerId, identify_info: &IdentifyInfo) -> bool{
		identify_info.protocol_version.contains("substrate")
	}
}

