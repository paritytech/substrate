#!/bin/bash

steps=50
repeat=20

chain=dev

pallets=(
	pallet_assets
	pallet_babe
	pallet_balances
	pallet_bounties
	pallet_collective
	pallet_contracts
	pallet_democracy
	pallet_election_provider_multi_phase
	pallet_elections_phragmen
	pallet_gilt
	pallet_identity
	pallet_im_online
	pallet_indices
	pallet_lottery
	pallet_membership
	pallet_mmr
	pallet_multisig
	pallet_offences
	pallet_proxy
	pallet_scheduler
	pallet_session
	pallet_staking
	frame_system
	pallet_timestamp
	pallet_tips
	pallet_transaction_storage
	pallet_treasury
	pallet_uniques
	pallet_utility
	pallet_vesting
)

folders=(
	assets
	babe
	balances
	bounties
	collective
	contracts
	democracy
	election-provider-multi-phase
	elections
	gilt
	identity
	im-online
	indices
	lottery
	membership
	mmr
	multisig
	offences
	proxy
	scheduler
	session
	staking
	system
	timestamp
	tips
	transaction-storage
	treasury
	uniques
	utility
	vesting
)

for p in ${!pallets[@]}
do
	pallet=${pallets[$p]}
	folder=${folders[$p]}

	target/release/substrate benchmark \
		--chain=$chain \
		--steps=$steps  \
		--repeat=$repeat \
		--pallet=$pallet  \
		--extrinsic='*' \
		--execution=wasm \
		--wasm-execution=compiled \
		--heap-pages=4096 \
		--output=./frame/$folder/src/weights.rs \
		--template=./.maintain/frame-weight-template.hbs
done
