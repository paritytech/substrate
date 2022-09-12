#!/bin/bash

#BINARY=substrate
BINARY=node-sassafras

TARGET=debug
#TARGET=release

PALLET=pallet_sassafras
EXTRINSIC=submit_tickets
STEPS=50
REPEAT=20

OUTFILE=output.rs

./target/$TARGET/$BINARY benchmark pallet \
    --chain dev \
    --execution wasm \
    --wasm-execution compiled \
    --pallet $PALLET \
    --extrinsic $EXTRINSIC \
    --steps $STEPS \
    --repeat $REPEAT \
    --output $OUTFILE
