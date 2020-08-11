#!/bin/bash

function rust_rename() {
    sed -i "s/$1/$2/g" `grep -Rl --include="*.rs" --include="*.stderr" "$1" *` > /dev/null
}

function cargo_rename() {
    find . -name "Cargo.toml" -exec sed -i "s/\(^\|[^\/]\)$1/\1$2/g" {} \;
}

function rename_gitlabci() {
    sed -i "s/$1/$2/g" .gitlab-ci.yml
}

function rename() {
    old=$(echo $1 | cut -f1 -d\ );
    new=$(echo $1 | cut -f2 -d\ );

    echo "Renaming $old to $new"
    # rename in Cargo.tomls
    cargo_rename $old $new
    rename_gitlabci $old $new
    # and it appears, we have the same syntax in rust files
    rust_rename $old $new

    # but generally we have the snail case syntax in rust files
    old=$(echo $old | sed s/-/_/g );
    new=$(echo $new | sed s/-/_/g );

    echo " > $old to $new"
    rust_rename $old $new
}

TO_RENAME=(
    # OLD-CRATE-NAME NEW-CRATE-NAME

    # post initial rename fixes
    "sc-application-crypto sp-application-crypto"
    "sp-transaction-pool-api sp-transaction-pool"
    "sp-transaction-pool-runtime-api sp-transaction-pool"
    "sp-core-storage sp-storage"
    "transaction-factory node-transaction-factory"
    "sp-finality-granpda sp-finality-grandpa"
    "sp-sesssion sp-session"
    "sp-tracing-pool sp-transaction-pool"
    "sc-basic-authority sc-basic-authorship"
    "sc-api sc-client-api"
    "sc-database sc-client-db"

    # PRIMITIVES
    "substrate-application-crypto sp-application-crypto"
    "substrate-authority-discovery-primitives sp-authority-discovery"
    "substrate-block-builder-runtime-api sp-block-builder"
    "substrate-consensus-aura-primitives sp-consensus-aura"
    "substrate-consensus-babe-primitives sp-consensus-babe"
    "substrate-consensus-common sp-consensus"
    "substrate-consensus-pow-primitives sp-consensus-pow"
    "substrate-primitives sp-core"
    "substrate-debug-derive sp-debug-derive"
    "substrate-primitives-storage sp-storage"
    "substrate-externalities sp-externalities"
    "substrate-finality-grandpa-primitives sp-finality-grandpa"
    "substrate-inherents sp-inherents"
    "substrate-keyring sp-keyring"
    "substrate-offchain-primitives sp-offchain"
    "substrate-panic-handler sp-panic-handler"
    "substrate-phragmen sp-npos-elections"
    "substrate-rpc-primitives sp-rpc"
    "substrate-runtime-interface sp-runtime-interface"
    "substrate-runtime-interface-proc-macro sp-runtime-interface-proc-macro"
    "substrate-runtime-interface-test-wasm sp-runtime-interface-test-wasm"
    "substrate-serializer sp-serializer"
    "substrate-session sp-session"
    "sr-api sp-api"
    "sr-api-proc-macro sp-api-proc-macro"
    "sr-api-test sp-api-test"
    "sr-arithmetic sp-arithmetic"
    "sr-arithmetic-fuzzer sp-arithmetic-fuzzer"
    "sr-io sp-io"
    "sr-primitives sp-runtime"
    "sr-sandbox sp-sandbox"
    "sr-staking-primitives sp-staking"
    "sr-std sp-std"
    "sr-version sp-version"
    "substrate-state-machine sp-state-machine"
    "substrate-transaction-pool-runtime-api sp-transaction-pool"
    "substrate-trie sp-trie"
    "substrate-wasm-interface sp-wasm-interface"

    # # CLIENT
    "substrate-client sc-client"
    "substrate-client-api sc-client-api"
    "substrate-authority-discovery sc-authority-discovery"
    "substrate-basic-authorship sc-basic-authorship"
    "substrate-block-builder sc-block-builder"
    "substrate-chain-spec sc-chain-spec"
    "substrate-chain-spec-derive sc-chain-spec-derive"
    "substrate-cli sc-cli"
    "substrate-consensus-aura sc-consensus-aura"
    "substrate-consensus-babe sc-consensus-babe"
    "substrate-consensus-pow sc-consensus-pow"
    "substrate-consensus-slots sc-consensus-slots"
    "substrate-consensus-uncles sc-consensus-uncles"
    "substrate-client-db sc-client-db"
    "substrate-executor sc-executor"
    "substrate-runtime-test sc-runtime-test"
    "substrate-finality-grandpa sc-finality-grandpa"
    "substrate-keystore sc-keystore"
    "substrate-network sc-network"
    "substrate-offchain sc-offchain"
    "substrate-peerset sc-peerset"
    "substrate-rpc-servers sc-rpc-server"
    "substrate-rpc sc-rpc"
    "substrate-service sc-service"
    "substrate-service-test sc-service-test"
    "substrate-state-db sc-state-db"
    "substrate-telemetry sc-telemetry"
    "substrate-test-primitives sp-test-primitives"
    "substrate-tracing sc-tracing"

);

for rule in "${TO_RENAME[@]}"
do
	rename "$rule";
done
