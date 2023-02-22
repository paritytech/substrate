#!/usr/bin/env bash

args=$@

# handle when arguments not provided. run arguments provided to script.
if [ "$args" = "" ] ; then
    su -c "printf \"Note: Please try providing an argument to the script.\n\n\"" nonroot
    exit 1
else
    printf \"*** Running Substrate Docker container with provided arguments: $args\n\n\"
    docker run --rm -it parity/substrate $args
fi

