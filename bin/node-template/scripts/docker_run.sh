#!/usr/bin/env bash
# This script is meant to be run on Unix/Linux based systems
set -e

printf "*** Start Substrate node template ***\n"
SCRIPT_DIR=$(realpath "$(dirname "${BASH_SOURCE[0]}")")
PARENT_DIR=$(dirname "$SCRIPT_DIR")
mkdir -p "$PARENT_DIR/.local"
mkdir -p "$PARENT_DIR/.cargo/registry"
cd $(dirname ${BASH_SOURCE[0]})/..

modify_first_line_of_docker_compose() {
    local first_line=$1
    sed -i "1s/.*/$first_line/" $PARENT_DIR/docker-compose.yml
}

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
        # temporarily comment out first line `services:` of ../docker-compose.yml
        modify_first_line_of_docker_compose "#services:"
        docker-compose down --remove-orphans
        docker-compose run --rm --service-ports dev $@
        # uncomment again the first line `services:` of ../docker-compose.yml
        modify_first_line_of_docker_compose "services:"
        exit
    fi

    exit_code=$(docker-compose compose version; status=$?; echo $status)
    last_char=${exit_code: -1}

    if [[ "x${last_char}" == "x0" && "$(docker-compose compose version)" =~ " v2." ]]; then
        printf "Detected legacy docker-compose version 2.x. Using Compose File Format 2+.\n"
        # switch back to default `services:` incase was temporarily commented out
        modify_first_line_of_docker_compose "services:"
        docker-compose compose down --remove-orphans
        docker-compose compose run --rm --service-ports dev $@
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
        # switch back to default `services:` incase was temporarily commented out
        modify_first_line_of_docker_compose "services:"
        docker compose down --remove-orphans
        docker compose run --rm --service-ports dev $@
    else
        printf "Skipping docker since docker executable subcommand not supported.\n"
    fi
    exit
fi

printf "Error: Unable to detect any docker compose installation.\n"
