#!/usr/bin/env python3
"""
verify.py — one command that either says PASS or explains why not.

Checks, in order:

  1. `lake build` — all Lean files elaborate under the pinned toolchain.
  2. no `sorry` in the sources, and no `sorryAx` in the axiom footprint of any
     checked theorem (the second check is the one that cannot be faked).
  3. the axiom footprint of every headline theorem equals what the project
     claims in lean/README.md — a proof that silently starts depending on a
     new axiom is a regression, not a detail.
  4. `witness/m0.py`, the differential witness, unless --skip-witness. It writes
     witness-manifest.json (seeds, counts, coverage, statistics) next to the repo
     root so a run can be reproduced exactly.

Usage:
    python scripts/verify.py                # everything
    python scripts/verify.py --quick        # smaller witness run
    python scripts/verify.py --skip-witness
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean"

# theorem -> sorted axiom list, exactly as `#print axioms` reports it.
EXPECTED: dict[str, dict[str, list[str]]] = {
    "Lemma1.lean": {
        "lemma1_seq_deterministic": [],
        "runSeq_sound": [],
        "seq_unique_result": [],
    },
    "Lemma2.lean": {
        "commit_evalBody": ["Quot.sound", "propext"],
        "par_refines_seq": ["Quot.sound", "propext"],
    },
    "Lemma3.lean": {
        "lemma3A_extension_preservation": ["Quot.sound", "propext"],
        "lemma3B_boundary_counterexample": ["propext"],
        "order_necessary": ["Quot.sound", "propext"],
        "validation_necessary": ["propext"],
        "par_progress": ["Quot.sound", "propext"],
    },
    "Lemma3_5.lean": {
        "lemma3_5_equiv_implies_observable": ["Quot.sound", "propext"],
        "same_journal_all_equiv": ["Quot.sound", "propext"],
    },
    "Lemma4.lean": {
        "substrate_independence": [],
        "implements_M0_execute_eq": [],
        "substrate_run_eq_seq": ["propext"],
        "trace_refines_seq": ["Quot.sound", "propext"],
        "wave_refines_seq": ["Quot.sound", "propext"],
        "cross_substrate_witness": ["Quot.sound", "propext"],
        "wave_partition_artifact": ["Quot.sound", "propext"],
    },
    "Lemma5.lean": {
        "fail_substrate_independence_eq": [],
        "runTrace_is_crashRun": [],
        "seq_out_prefix": ["propext"],
        "fail_substrate_independence": ["propext"],
        "fail_observable_prefix": ["propext"],
        "substrate_independence_of_fail": ["propext"],
        "crash_forced_prefix": ["propext"],
        "crash_prefix_witness": ["propext"],
        "crash_refines_seq": ["Quot.sound", "propext"],
        "crash_prefix_witness_vs_seq": ["Quot.sound", "propext"],
        "crash_complete": ["Quot.sound", "propext"],
    },
}

AXIOM_LINE = re.compile(r"^'(?P<name>[^']+)' (?:depends on axioms: \[(?P<axioms>[^\]]*)\]|"
                        r"does not depend on any axioms)$")
# `sorry` as a token, ignoring the string "sorry" inside comments is not worth the
# complexity: a comment mentioning it is also worth a look.
SORRY = re.compile(r"\bsorry\b")


def run(cmd: list[str], cwd: Path = ROOT) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)


def step(label: str) -> None:
    print(f"── {label}", flush=True)


def check_build() -> list[str]:
    step("lake build")
    r = run(["lake", "build"])
    out = r.stdout + r.stderr
    print(out.rstrip() or "  (no output)")
    fails = []
    if r.returncode != 0:
        fails.append("lake build failed")
    if "declaration uses 'sorry'" in out:
        fails.append("build reports a declaration using sorry")
    return fails


def check_sorry() -> list[str]:
    step("no sorry in sources")
    fails = []
    for f in sorted(LEAN_DIR.glob("*.lean")):
        hits = [i for i, line in enumerate(f.read_text().splitlines(), 1) if SORRY.search(line)]
        if hits:
            fails.append(f"{f.name}: sorry on lines {hits}")
        print(f"  {f.name:<16} clean" if not hits else f"  {f.name:<16} SORRY")
    return fails


def check_axioms() -> list[str]:
    step("axiom footprint")
    fails = []
    for fname, expected in EXPECTED.items():
        src = LEAN_DIR / fname
        if not src.exists():
            fails.append(f"{fname}: missing")
            continue
        probe = "\n".join(f"#print axioms {name}" for name in expected)
        with tempfile.TemporaryDirectory() as tmp:
            copy = Path(tmp) / fname
            copy.write_text(src.read_text() + "\n\n" + probe + "\n")
            r = run(["lean", str(copy)], cwd=Path(tmp))
        if r.returncode != 0:
            fails.append(f"{fname}: lean exited {r.returncode}\n{r.stdout}{r.stderr}")
            continue
        got: dict[str, list[str]] = {}
        for line in r.stdout.splitlines():
            m = AXIOM_LINE.match(line.strip())
            if m:
                axioms = m.group("axioms")
                got[m.group("name")] = sorted(a.strip() for a in axioms.split(",")) if axioms else []
        for name, want in expected.items():
            have = got.get(name)
            if have is None:
                fails.append(f"{fname}: no axiom report for {name}")
            elif "sorryAx" in have:
                fails.append(f"{fname}: {name} depends on sorryAx")
            elif have != sorted(want):
                fails.append(f"{fname}: {name} axioms {have}, expected {sorted(want)}")
            else:
                shown = ", ".join(have) if have else "none"
                print(f"  {name:<34} {shown}")
    return fails


def check_witness(quick: bool) -> list[str]:
    step("witness")
    args = ["python3", "witness/m0.py", "all", "--manifest", "witness-manifest.json"]
    if quick:
        args += ["--n-a", "20", "--n-b", "300", "--n-c", "300", "--n-neg", "100"]
    r = run(args)
    print((r.stdout + r.stderr).rstrip())
    if r.returncode != 0 or "ALL CHECKS PASSED" not in r.stdout:
        return ["witness did not pass"]
    return []


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="smaller witness run")
    ap.add_argument("--skip-witness", action="store_true")
    args = ap.parse_args()

    fails: list[str] = []
    fails += check_build()
    fails += check_sorry()
    fails += check_axioms()
    if not args.skip_witness:
        fails += check_witness(args.quick)

    print()
    if fails:
        print("FAIL")
        for f in fails:
            print(f"  - {f}")
        return 1
    print("PASS — build clean, 0 sorry, axiom footprint as documented"
          + ("" if args.skip_witness else ", witness green"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
