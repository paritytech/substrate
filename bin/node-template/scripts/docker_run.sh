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

if ! [ -x "$(command -v docker-compose)" ]; then
    printf "Skipping docker-compose since executable is not installed.\n"
else
    printf "Detected docker-compose executable.\n"
    exit_code=$(docker-compose version; status=$?; echo $status)
    # get the last character captured by $? since it may also include command output first
    last_char=${exit_code: -1}

    # prefix last char with random character incase last char is 0 but not an exit code
    if [[ "x${last_char}" == "x0" && "$(docker-compose version)" =~ " 1." ]]; then
        printf "Detected legacy docker-compose version 1.x. Using Compose File Format 1.\n"
        docker-compose -f docker-compose-legacy.yml down --remove-orphans
        docker-compose -f docker-compose-legacy.yml run --rm --service-ports dev $@
        exit
    fi

    exit_code=$(docker-compose compose version; status=$?; echo $status)
    last_char=${exit_code: -1}

    if [[ "x${last_char}" == "x0" && "$(docker-compose compose version)" =~ " v2." ]]; then
        printf "Detected legacy docker-compose version 2.x. Using Compose File Format 2+.\n"
        docker-compose compose -f docker-compose-legacy.yml down --remove-orphans
        docker-compose compose -f docker-compose-legacy.yml run --rm --service-ports dev $@
        exit
    fi

    printf "Unknown or unsupported version of docker-compose. Skipping...\n"
fi

if ! [ -x "$(command -v docker)" ]; then
    printf "Skipping docker since docker executable is not installed.\n"
else
    printf "Detected docker executable.\n"
    exit_code=$(docker compose version; status=$?; echo $status)
    last_char=${exit_code: -1}

    if [[ "x${last_char}" == "x0" ]]; then
        printf "Detected docker compose subcommand.\n"
        # TOD0 modify the docker-compose-legacy.yml file to inject `services:` on first line
        docker compose -f docker-compose-legacy.yml down --remove-orphans
        docker compose -f docker-compose-legacy.yml run --rm --service-ports dev $@
    else
        printf "Skipping docker since docker executable subcommand not supported.\n"
    fi
    exit
fi

printf "Error: Unable to detect any docker compose installation.\n"
