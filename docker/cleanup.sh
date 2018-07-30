#!/usr/bin/env bash
# This script helps reduce the size of the built image
# It removes data that is not required.

export PATH=$PATH:$HOME/.cargo/bin

cargo clean
rm -rf /root/.cargo /root/.rustup /tmp/*
