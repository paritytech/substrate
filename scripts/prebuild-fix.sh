#!/bin/zsh

files=( $(compgen -G "$HOME/.cargo/registry/src/github.com-*/wasmtime-runtime-0.19.0/src/traphandlers.rs") )

if [ ! -z "$files" ]; then
    echo "Found file $files"
    sed -i '' 's/__rip/__pc/g' $files
fi
