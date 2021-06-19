#!/bin/bash

steps=50
repeat=20

chain=dev

pallets=(
	pallet_balances
	pallet_bounties
)

folders=(
	balances
	bounties
)

for p in ${!pallets[@]}
do
	pallet = ${pallets[$p]}
	folder = ${folders[$p]}

	target/release/polkadot benchmark \
		--chain=$chain \
		--steps=$steps  \
		--repeat=$repeat \
		--pallet=$pallet  \
		--extrinsic='*' \
		--execution=wasm \
		--wasm-execution=compiled \
		--heap-pages=4096 \
		--output=./frame/$folder/src/weights.rs
		--template=./.maintain/frame-weight-template.hbs
done
