// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! TODO doc

mod event_format;
mod layers;

use tracing::Subscriber;
use tracing_subscriber::{
	filter::Directive, fmt::time::ChronoLocal, layer::SubscriberExt, registry::LookupSpan,
	FmtSubscriber, Layer,
};

pub use event_format::*;
pub use layers::*;

/// Initialize the global logger TODO update doc
///
/// This sets various global logging and tracing instances and thus may only be called once.
pub fn get_default_subscriber_and_telemetries(
	pattern: &str,
	telemetry_external_transport: Option<sc_telemetry::ExtTransport>,
) -> std::result::Result<
	(
		impl Subscriber + for<'a> LookupSpan<'a>,
		sc_telemetry::Telemetries,
	),
	String,
> {
	get_default_subscriber_and_telemetries_internal(
		parse_directives(pattern),
		telemetry_external_transport,
	)
}

/// Initialize the global logger TODO update doc
///
/// This sets various global logging and tracing instances and thus may only be called once.
pub fn get_default_subscriber_and_telemetries_with_profiling(
	pattern: &str,
	telemetry_external_transport: Option<sc_telemetry::ExtTransport>,
	tracing_receiver: sc_tracing::TracingReceiver,
	profiling_targets: &str,
) -> std::result::Result<
	(
		impl Subscriber + for<'a> LookupSpan<'a>,
		sc_telemetry::Telemetries,
	),
	String,
> {
	let (subscriber, telemetries) = get_default_subscriber_and_telemetries_internal(
		parse_directives(pattern)
			.into_iter()
			.chain(parse_directives(profiling_targets).into_iter()),
		telemetry_external_transport,
	)?;
	let profiling = sc_tracing::ProfilingLayer::new(tracing_receiver, profiling_targets);

	Ok((subscriber.with(profiling), telemetries))
}

fn get_default_subscriber_and_telemetries_internal(
	extra_directives: impl IntoIterator<Item = Directive>,
	telemetry_external_transport: Option<sc_telemetry::ExtTransport>,
) -> std::result::Result<
	(
		impl Subscriber + for<'a> LookupSpan<'a>,
		sc_telemetry::Telemetries,
	),
	String,
> {
	if let Err(e) = tracing_log::LogTracer::init() {
		return Err(format!("Registering Substrate logger failed: {:}!", e));
	}

	let mut env_filter = tracing_subscriber::EnvFilter::default()
		// Disable info logging by default for some modules.
		.add_directive("ws=off".parse().expect("provided directive is valid"))
		.add_directive("yamux=off".parse().expect("provided directive is valid"))
		.add_directive(
			"cranelift_codegen=off"
				.parse()
				.expect("provided directive is valid"),
		)
		// Set warn logging by default for some modules.
		.add_directive(
			"cranelift_wasm=warn"
				.parse()
				.expect("provided directive is valid"),
		)
		.add_directive("hyper=warn".parse().expect("provided directive is valid"))
		// Enable info for others.
		.add_directive(tracing_subscriber::filter::LevelFilter::INFO.into());

	if let Ok(lvl) = std::env::var("RUST_LOG") {
		if lvl != "" {
			// We're not sure if log or tracing is available at this moment, so silently ignore the
			// parse error.
			for directive in parse_directives(lvl) {
				env_filter = env_filter.add_directive(directive);
			}
		}
	}

	for directive in extra_directives {
		// We're not sure if log or tracing is available at this moment, so silently ignore the
		// parse error.
		env_filter = env_filter.add_directive(directive);
	}

	// If we're only logging `INFO` entries then we'll use a simplified logging format.
	let simple = match Layer::<FmtSubscriber>::max_level_hint(&env_filter) {
		Some(level) if level <= tracing_subscriber::filter::LevelFilter::INFO => true,
		_ => false,
	};

	// Always log the special target `sc_tracing`, overrides global level.
	// NOTE: this must be done after we check the `max_level_hint` otherwise
	// it is always raised to `TRACE`.
	env_filter = env_filter.add_directive(
		"sc_tracing=trace"
			.parse()
			.expect("provided directive is valid"),
	);

	let isatty = atty::is(atty::Stream::Stderr);
	let enable_color = isatty;
	let timer = ChronoLocal::with_format(if simple {
		"%Y-%m-%d %H:%M:%S".to_string()
	} else {
		"%Y-%m-%d %H:%M:%S%.3f".to_string()
	});

	let telemetries = if let Some(telemetry_external_transport) = telemetry_external_transport {
		sc_telemetry::Telemetries::with_wasm_external_transport(telemetry_external_transport)
	} else {
		Default::default()
	};
	let senders = telemetries.senders();
	let telemetry_layer = sc_telemetry::TelemetryLayer::new(senders);
	let event_format = EventFormat {
		timer,
		ansi: enable_color,
		display_target: !simple,
		display_level: !simple,
		display_thread_name: !simple,
	};
	let builder = FmtSubscriber::builder()
		.with_env_filter(env_filter)
		.with_writer(
			#[cfg(not(target_os = "unknown"))]
			std::io::stderr,
			#[cfg(target_os = "unknown")]
			std::io::sink,
		);

	#[cfg(not(target_os = "unknown"))]
	let builder = builder.event_format(event_format);

	let subscriber = builder.finish().with(PrefixLayer).with(telemetry_layer);

	#[cfg(target_os = "unknown")]
	let subscriber = subscriber.with(ConsoleLogLayer::new(event_format));

	Ok((subscriber, telemetries))
}

fn parse_directives(dirs: impl AsRef<str>) -> Vec<Directive> {
	let dirs = dirs.as_ref();

	if dirs.is_empty() {
		return Default::default();
	}

	dirs.split(',').filter_map(|s| s.parse().ok()).collect()
}
