// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use futures::{stream::unfold, FutureExt, Stream, StreamExt};
use futures_timer::Delay;
use std::time::Duration;

pub fn interval(duration: Duration) -> impl Stream<Item = ()> + Unpin {
    unfold((), move |_| Delay::new(duration).map(|_| Some(((), ())))).map(drop)
}
