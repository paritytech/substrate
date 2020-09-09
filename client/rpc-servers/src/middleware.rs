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

//! Middlewares for RPC servers.

use http::{RequestMiddleware as HttpRequestMiddleware, RequestMiddlewareAction as HttpRequestMiddlewareAction};
use hyper::Body;
use ws::{RequestMiddleware as WSRequestMiddleware, MiddlewareAction as WSRequestMiddlewareAction};

pub struct HttpRpcMiddleware {}

impl HttpRpcMiddleware {
	pub fn new() -> Self {
		HttpRpcMiddleware {}
	}
}

impl HttpRequestMiddleware for HttpRpcMiddleware {
	fn on_request(&self, request: hyper::Request<Body>) -> HttpRequestMiddlewareAction {
		HttpRequestMiddlewareAction::Proceed {
			should_continue_on_invalid_cors: false,
			request,
		}
	}
}

pub struct WSRpcMiddleware {}

impl WSRpcMiddleware {
	pub fn new() -> Self {
		WSRpcMiddleware {}
	}
}

impl WSRequestMiddleware for WSRpcMiddleware {
	fn process(&self, req: &ws_core::Request) -> WSRequestMiddlewareAction {
		WSRequestMiddlewareAction::Proceed
	}
}
