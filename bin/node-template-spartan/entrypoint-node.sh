#!/usr/bin/env bash
set -e

source /root/.cargo/env

exec cargo run --bin node-template-spartan -- --dev --tmp --ws-external
