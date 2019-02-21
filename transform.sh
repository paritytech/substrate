#!/bin/bash 

set -euo pipefail

# expose these methods by their non-mangled names
sed -i 's/static u64 BlockBuilder/u64 BlockBuilder/g' node_runtime.c
sed -i 's/static u64 Grandpa/u64 Grandpa/g' node_runtime.c
sed -i 's/static u64 Core/u64 Core/g' node_runtime.c
sed -i 's/static u64 Aura/u64 Aura/g' node_runtime.c
sed -i 's/static u64 Tagged/u64 Tagged/g' node_runtime.c
sed -i 's/static u64 Metadata/u64 Metadata/g' node_runtime.c

# allocate 100 pages initially (instead of 17)
sed -i 's/17, 65536/100, 65536/g' node_runtime.c

# ensure methods can be called by their non-mangled name from rust
sed -i 's/\*Z/Z/g' node_runtime.h

# add a module prefix (e.g. the init method is then exported
# as node_runtime_init).
echo "#define WASM_RT_MODULE_PREFIX node_runtime_" > /tmp/tmpnode_runtime.c
cat node_runtime.c >> /tmp/tmpnode_runtime.c
mv /tmp/tmpnode_runtime.c node_runtime.c
