#!/usr/bin/env bash

(cd ../ && tar c docker/Deps.dockerfile docker/touch_libs.sh $(find . -name "Cargo.lock") $(find . -name "Cargo.toml") $(find . -name "bench.rs") | docker build -t substrate-deps -f docker/Deps.dockerfile -)
(cd ../ && docker build -f docker/Substrate.dockerfile .)
