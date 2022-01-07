// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use sc_utils::notification::{NotificationSender, NotificationStream, TracingKeyStr};

use crate::justification::GrandpaJustification;

/// The sending half of the Grandpa justification channel(s).
///
/// Used to send notifications about justifications generated
/// at the end of a Grandpa round.
pub type GrandpaJustificationSender<Block> = NotificationSender<GrandpaJustification<Block>>;

/// The receiving half of the Grandpa justification channel.
///
/// Used to receive notifications about justifications generated
/// at the end of a Grandpa round.
/// The `GrandpaJustificationStream` entity stores the `SharedJustificationSenders`
/// so it can be used to add more subscriptions.
pub type GrandpaJustificationStream<Block> =
	NotificationStream<GrandpaJustification<Block>, GrandpaJustificationsTracingKey>;

/// Provides tracing key for GRANDPA justifications stream.
#[derive(Clone)]
pub struct GrandpaJustificationsTracingKey;
impl TracingKeyStr for GrandpaJustificationsTracingKey {
	const TRACING_KEY: &'static str = "mpsc_grandpa_justification_notification_stream";
}
