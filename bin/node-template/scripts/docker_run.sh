#!/usr/bin/env bash
# This script is meant to be run on Unix/Linux based systems
set -e

printf "*** Start Substrate node template ***\n"

SCRIPT_DIR=$(realpath "$(dirname "${BASH_SOURCE[0]}")")
PARENT_DIR=$(dirname "$SCRIPT_DIR")
mkdir -p "$PARENT_DIR/.local"
mkdir -p "$PARENT_DIR/.cargo/registry"

cd $(dirname ${BASH_SOURCE[0]})/..

printf "Searching for docker-compose executable...\n"
# docker/compose v1
if ! [ -x "$(command -v docker-compose)" ]; then
    printf "Skipping docker-compose since executable is not installed.\n"
else
    printf "Detected docker-compose executable.\n"
    docker-compose down --remove-orphans
    docker-compose run --rm --service-ports dev $@
    exit
fi

# docker/compose v2
if ! [ -x "$(command -v docker)" ]; then
    printf "Skipping docker since docker executable is not installed.\n"
else
    printf "Detected docker executable.\n"
    exit_code=$(docker compose version &> /dev/null && echo $?)
    if [ $exit_code == "0" ]; then
        printf "Detected docker compose subcommand.\n"
        docker compose down --remove-orphans
        docker compose run --rm --service-ports dev $@
    else
        printf "Skipping docker since docker executable subcommand not supported.\n"
    fi
    exit
fi

printf "Error: Unable to detect docker compose installation."
