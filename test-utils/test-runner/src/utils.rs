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

/// Base db path gotten from env
pub fn base_path() -> Option<String> {
	std::env::var("DB_BASE_PATH").ok()
}

/// Builds the global logger.
pub fn logger<LogSink>(executor: tokio::runtime::Handle, log_sink: LogSink)
where
	LogSink: Sink<String> + Clone + Unpin + Send + Sync + 'static,
	LogSink::Error: Send + Sync + fmt::Debug,
{
	let ignore = [
		"yamux",
		"multistream_select",
		"libp2p",
		"jsonrpc_client_transports",
		"sc_network",
		"tokio_reactor",
		"parity-db",
		"sub-libp2p",
		"sync",
		"peerset",
		"ws",
		"sc_network",
		"sc_service",
		"sc_basic_authorship",
		"telemetry-logger",
		"sc_peerset",
		"rpc",
	];
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
	builder.filter_level(log::LevelFilter::Debug);
	builder.filter_module("runtime", log::LevelFilter::Trace);
	builder.filter_module("babe", log::LevelFilter::Info);
	builder.filter_module("sc_service", log::LevelFilter::Trace);
	for module in &ignore {
		builder.filter_module(module, log::LevelFilter::Off);
	}
	let _ = builder.is_test(true).try_init();
}
