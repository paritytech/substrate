// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use super::*;

mockall::mock! {
	pub ImportQueueHandle<B: BlockT> {}

	impl<B: BlockT> ImportQueueService<B> for ImportQueueHandle<B> {
		fn import_blocks(&mut self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>);
		fn import_justifications(
			&mut self,
			who: RuntimeOrigin,
			hash: B::Hash,
			number: NumberFor<B>,
			justifications: Justifications,
		);
	}
}

mockall::mock! {
	pub ImportQueue<B: BlockT> {}

	#[async_trait::async_trait]
	impl<B: BlockT> ImportQueue<B> for ImportQueue<B> {
		fn service(&self) -> Box<dyn ImportQueueService<B>>;
		fn service_ref(&mut self) -> &mut dyn ImportQueueService<B>;
		fn poll_actions<'a>(&mut self, cx: &mut futures::task::Context<'a>, link: &mut dyn Link<B>);
		async fn run(self, link: Box<dyn Link<B>>);
	}
}
