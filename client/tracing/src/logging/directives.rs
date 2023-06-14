// Copyright Parity Technologies (UK) Ltd.
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

use once_cell::sync::OnceCell;
use parking_lot::Mutex;
use tracing_subscriber::{
	filter::Directive, fmt as tracing_fmt, layer, reload::Handle, EnvFilter, Registry,
};

// Handle to reload the tracing log filter
static FILTER_RELOAD_HANDLE: OnceCell<Handle<EnvFilter, SCSubscriber>> = OnceCell::new();
// Directives that are defaulted to when resetting the log filter
static DEFAULT_DIRECTIVES: OnceCell<Mutex<Vec<String>>> = OnceCell::new();
// Current state of log filter
static CURRENT_DIRECTIVES: OnceCell<Mutex<Vec<String>>> = OnceCell::new();

/// Add log filter directive(s) to the defaults
///
/// The syntax is identical to the CLI `<target>=<level>`:
///
/// `sync=debug,state=trace`
pub(crate) fn add_default_directives(directives: &str) {
	DEFAULT_DIRECTIVES
		.get_or_init(|| Mutex::new(Vec::new()))
		.lock()
		.push(directives.to_owned());
	add_directives(directives);
}

/// Add directives to current directives
pub fn add_directives(directives: &str) {
	CURRENT_DIRECTIVES
		.get_or_init(|| Mutex::new(Vec::new()))
		.lock()
		.push(directives.to_owned());
}

/// Parse `Directive` and add to default directives if successful.
///
/// Ensures the supplied directive will be restored when resetting the log filter.
pub(crate) fn parse_default_directive(directive: &str) -> super::Result<Directive> {
	let dir = directive.parse()?;
	add_default_directives(directive);
	Ok(dir)
}

/// Reload the logging filter with the supplied directives added to the existing directives
pub fn reload_filter() -> Result<(), String> {
	let mut env_filter = EnvFilter::default();
	if let Some(current_directives) = CURRENT_DIRECTIVES.get() {
		// Use join and then split in case any directives added together
		for directive in current_directives.lock().join(",").split(',').map(|d| d.parse()) {
			match directive {
				Ok(dir) => env_filter = env_filter.add_directive(dir),
				Err(invalid_directive) => {
					log::warn!(
						target: "tracing",
						"Unable to parse directive while setting log filter: {:?}",
						invalid_directive,
					);
				},
			}
		}
	}

	// Set the max logging level for the `log` macros.
	let max_level_hint =
		tracing_subscriber::Layer::<tracing_subscriber::FmtSubscriber>::max_level_hint(&env_filter);
	log::set_max_level(super::to_log_level_filter(max_level_hint));

	log::debug!(target: "tracing", "Reloading log filter with: {}", env_filter);
	FILTER_RELOAD_HANDLE
		.get()
		.ok_or("No reload handle present")?
		.reload(env_filter)
		.map_err(|e| format!("{}", e))
}

/// Resets the log filter back to the original state when the node was started.
///
/// Includes substrate defaults and CLI supplied directives.
pub fn reset_log_filter() -> Result<(), String> {
	let directive = DEFAULT_DIRECTIVES.get_or_init(|| Mutex::new(Vec::new())).lock().clone();

	*CURRENT_DIRECTIVES.get_or_init(|| Mutex::new(Vec::new())).lock() = directive;
	reload_filter()
}

/// Initialize FILTER_RELOAD_HANDLE, only possible once
pub(crate) fn set_reload_handle(handle: Handle<EnvFilter, SCSubscriber>) {
	let _ = FILTER_RELOAD_HANDLE.set(handle);
}

// The layered Subscriber as built up in `LoggerBuilder::init()`.
// Used in the reload `Handle`.
type SCSubscriber<
	N = tracing_fmt::format::DefaultFields,
	E = crate::logging::EventFormat,
	W = crate::logging::DefaultLogger,
> = layer::Layered<tracing_fmt::Layer<Registry, N, E, W>, Registry>;
