// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use futures::{Sink, SinkExt};
use std::fmt;
use std::io::Write;
use log::LevelFilter;

/// Base db path gotten from env
pub fn base_path() -> Option<String> {
	std::env::var("DB_BASE_PATH").ok()
}

/// Builds the global logger.
pub fn logger<S>(
	log_targets: Vec<(&'static str, LevelFilter)>,
	executor: tokio::runtime::Handle,
	log_sink: S,
)
where
	S: Sink<String> + Clone + Unpin + Send + Sync + 'static,
	S::Error: Send + Sync + fmt::Debug,
{
	let mut builder = env_logger::builder();
	builder.format(move |buf: &mut env_logger::fmt::Formatter, record: &log::Record| {
		let entry = format!("{} {} {}", record.level(), record.target(), record.args());
		let res = writeln!(buf, "{}", entry);

		let mut log_sink_clone = log_sink.clone();
		let _ = executor.spawn(async move {
			log_sink_clone.send(entry).await.expect("log_stream is dropped");
		});
		res
	});
	builder.write_style(env_logger::WriteStyle::Always);

	for (module, level) in log_targets {
		builder.filter_module(module, level);
	}
	let _ = builder.is_test(true).try_init();
}
