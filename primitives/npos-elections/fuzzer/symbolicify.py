#!/usr/bin/env python3

import string
import sys
import re

IDENT = re.compile(r"(\s*)(\d+),")
assert IDENT.groups == 2


def divmod_excel(n):
    a, b = divmod(n, 26)
    if b == 0:
        return a - 1, b + 26
    return a, b


def to_excel(num):
    chars = []
    while num > 0:
        num, d = divmod_excel(num)
        chars.append(string.ascii_uppercase[d - 1])
    return "".join(reversed(chars))


def ids_for(type_id):
    id = 0
    while True:
        id += 1
        yield f"{type_id}_{to_excel(id)}"

def subs(candidates, voters, line):
    "Make appropriate substitutions in the line according to candidate and voter symbolic ids"
    for dictionary in [candidates, voters]:
        for regex, symbolic in dictionary.items():
            line = regex.sub(symbolic, line)
    return line


def main():
    candidates = {}
    voters = {}
    candidate_ids = ids_for("Cand")
    voter_ids = ids_for("Voter")

    candidate_mode = False
    voter_mode = False
    voter_ident = None

    for line in sys.stdin:
        line = line.rstrip()

        # mode switch
        if "&candidates =" in line:
            candidate_mode = True
            print(line)
            continue
        elif '&voters = ' in line:
            voter_mode = True
            print(line)
            continue
        elif voter_mode and line.strip() == '),':
            voter_ident = None
            print(line)
            continue
        elif (candidate_mode or voter_mode) and line.strip() == ']':
            candidate_mode = False
            voter_mode = False
            voter_ident = None
            print(line)
            continue

        if candidate_mode:
            match = IDENT.match(line)
            whitespace = match.group(1)
            id = match.group(2)
            symbolic = next(candidate_ids)
            candidates[re.compile(f'\\b{id}\\b')] = symbolic
            print(f"{whitespace}{symbolic}, // {id}")
        elif voter_mode:
            found_match = False
            if voter_ident is None:
                if match := IDENT.match(line):
                    found_match = True
                    whitespace = match.group(1)
                    id = match.group(2)
                    voter_ident = id
                    symbolic = next(voter_ids)
                    voters[re.compile(f'\\b{id}\\b')] = symbolic
                    print(f"{whitespace}{symbolic}, // {id}")
            if not found_match:
                print(subs(candidates, voters, line))
        else:
            print(subs(candidates, voters, line))





if __name__ == '__main__':
    main()
