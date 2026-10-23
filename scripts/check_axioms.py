#!/usr/bin/env python3
"""Check the output of `lake env lean Challenges/AFreeMeasures/AxiomsAudit.lean`.

usage: check_axioms.py LOG AUDIT_SOURCE
Every declaration named by a `#print axioms` line of AUDIT_SOURCE must be reported, and each may
depend only on propext, Classical.choice and Quot.sound. Lean wraps long axiom lists over several
lines, so the whole log is parsed.
"""
import re, sys
log = open(sys.argv[1], encoding="utf-8").read()
source = open(sys.argv[2], encoding="utf-8").read()
expected = re.findall(r"^#print axioms\s+(\S+)", source, re.MULTILINE)
allowed = {"propext", "Classical.choice", "Quot.sound"}
found = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    found[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
for m in re.finditer(r"'([^']+)' does not depend on any axioms", log):
    found[m.group(1)] = set()
failed = not expected
for name in expected:
    if name not in found:
        print(f"FAIL {name}: no axiom report"); failed = True
    elif not found[name] <= allowed:
        print(f"FAIL {name}: unexpected axioms {sorted(found[name] - allowed)}"); failed = True
    else:
        print(f"ok   {name}: {sorted(found[name])}")
print(f"{len(expected)} declarations audited")
sys.exit(1 if failed else 0)
