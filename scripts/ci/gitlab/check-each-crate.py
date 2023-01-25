#!/usr/bin/env python3

# A script that checks each workspace crate individually.
# It's relevant to check workspace crates individually because otherwise their compilation problems
# due to feature misconfigurations won't be caught, as exemplified by
# https://github.com/paritytech/substrate/issues/12705

import subprocess, sys

# Get all crates
output = subprocess.check_output(["cargo", "tree", "--workspace", "--depth", "0", "--prefix", "none"])

# Convert the output into a proper list
crates = []
for line in output.splitlines():
	if line != b"":
		crates.append(line.decode('utf8').split(" ")[0])

# Make the list unique and sorted
crates = list(set(crates))
crates.sort()

target_group = int(sys.argv[1]) - 1
groups_total = int(sys.argv[2])

if len(crates) == 0:
	print("No crates detected!")
	sys.exit(1)

print(f"Total crates: {len(crates)}")

crates_per_group = (len(crates) + groups_total - 1) // groups_total

print(f"Crates per group: {crates_per_group}")

# Check each crate
for i in range(0, crates_per_group):
	print(f"Checking {crates[crates_per_group * target_group + i]}")

	res = subprocess.run(
		["cargo", "check", "--locked", "-p", crates[crates_per_group * target_group + i]],
	)

	if res.returncode != 0:
		sys.exit(1)
