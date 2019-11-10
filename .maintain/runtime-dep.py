#!/usr/bin/env python3

# To run this script, you need to install the 'toml' python package and install the 'graphviz' package:
# pip install toml
# sudo apt-get install graphviz
# the first parameter is the runtime folder
# python ./.maintain/runtime-dep.py ./substrate/runtime | dot -Tpng -o output.png
import sys
import os
import toml

if len(sys.argv) != 2:
    print("needs the runtime folder.")
    sys.exit(-1)

runtime_dir = sys.argv[1]

files = [os.path.join(runtime_dir, f, 'Cargo.toml') for f in os.listdir(runtime_dir) if os.path.isfile(os.path.join(runtime_dir, f, 'Cargo.toml')) and f != 'example']

print("digraph G {")


PREFIX = "substrate-runtime-"

for f in files:
    manifest = toml.load(f)

    package_name = manifest['package']['name']
    deps = [d for d in manifest['dependencies'].keys() if d.startswith(PREFIX)]

    for d in deps:
        print("    \"{}\" -> \"{}\";".format(package_name, d))

print("}")
