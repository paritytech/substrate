#!/usr/bin/env sh

for manifest in $(find . -mindepth 2 -name "Cargo.toml")
do
    mkdir $(dirname ${manifest})/src
    touch $(dirname ${manifest})/src/lib.rs
done
