// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use crate::logging::event_format::{CustomFmtContext, EventFormat};
use std::fmt;
use tracing::{Event, Level, Subscriber};
use tracing_subscriber::{
	fmt::{
		time::{FormatTime, SystemTime},
		FormatFields,
	},
	layer::Context,
	registry::LookupSpan,
	Layer,
};
use wasm_bindgen::prelude::*;

/// A `Layer` that display logs in the browser's console.
pub struct ConsoleLogLayer<S, N = tracing_subscriber::fmt::format::DefaultFields, T = SystemTime> {
	event_format: EventFormat<T>,
	fmt_fields: N,
	_inner: std::marker::PhantomData<S>,
}

impl<S, T> ConsoleLogLayer<S, tracing_subscriber::fmt::format::DefaultFields, T> {
	/// Create a new [`ConsoleLogLayer`] using the `EventFormat` provided in argument.
	pub fn new(event_format: EventFormat<T>) -> Self {
		Self {
			event_format,
			fmt_fields: Default::default(),
			_inner: std::marker::PhantomData,
		}
	}
}

// NOTE: the following code took inspiration from `EventFormat` (in this file)
impl<S, N, T: FormatTime> ConsoleLogLayer<S, N, T>
where
	S: Subscriber + for<'a> LookupSpan<'a>,
	N: for<'writer> FormatFields<'writer> + 'static,
{
	fn format_event(
		&self,
		ctx: &Context<'_, S>,
		writer: &mut dyn fmt::Write,
		event: &Event,
	) -> fmt::Result {
		self.event_format.format_event_custom(
			CustomFmtContext::ContextWithFormatFields(ctx, &self.fmt_fields),
			writer,
			event,
		)
	}
}

// NOTE: the following code took inspiration from tracing-subscriber
//
//       https://github.com/tokio-rs/tracing/blob/2f59b32/tracing-subscriber/src/fmt/fmt_layer.rs#L717
impl<S, N, T> Layer<S> for ConsoleLogLayer<S, N, T>
where
	S: Subscriber + for<'a> LookupSpan<'a>,
	N: for<'writer> FormatFields<'writer> + 'static,
	T: FormatTime + 'static,
{
	fn on_event(&self, event: &Event<'_>, ctx: Context<'_, S>) {
		thread_local! {
			static BUF: std::cell::RefCell<String> = std::cell::RefCell::new(String::new());
		}

		BUF.with(|buf| {
			let borrow = buf.try_borrow_mut();
			let mut a;
			let mut b;
			let mut buf = match borrow {
				Ok(buf) => {
					a = buf;
					&mut *a
				}
				_ => {
					b = String::new();
					&mut b
				}
			};

			if self.format_event(&ctx, &mut buf, event).is_ok() {
				if !buf.is_empty() {
					let meta = event.metadata();
					let level = meta.level();
					// NOTE: the following code took inspiration from tracing-subscriber
					//
					//       https://github.com/iamcodemaker/console_log/blob/f13b5d6755/src/lib.rs#L149
					match *level {
						Level::ERROR => web_sys::console::error_1(&JsValue::from(buf.as_str())),
						Level::WARN => web_sys::console::warn_1(&JsValue::from(buf.as_str())),
						Level::INFO => web_sys::console::info_1(&JsValue::from(buf.as_str())),
						Level::DEBUG => web_sys::console::log_1(&JsValue::from(buf.as_str())),
						Level::TRACE => web_sys::console::debug_1(&JsValue::from(buf.as_str())),
					}
				}
			}

			buf.clear();
		});
	}
}
