#!/usr/bin/env python3
"""Run the selected axiom report and fail on missing queries or extra axioms."""
import argparse
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def parse_report(output):
    reports = {}
    for name, axioms in re.findall(r"^'(.+)' depends on axioms:\s*\[([^\]]*)\]", output, re.M):
        reports[name] = {x.strip() for x in axioms.split(",") if x.strip()}
    for name in re.findall(r"^'(.+)' does not depend on any axioms$", output, re.M):
        reports[name] = set()
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / ".build-audit/axioms")
    args = parser.parse_args()
    source = ROOT / "scripts" / "AxiomAudit.lean"
    expected = set(re.findall(r"^#print axioms (\S+)", source.read_text(), re.M))
    if not expected:
        raise SystemExit("No axiom queries found")
    command = ["lake", "env", "lean", "-j1", "-M14000", str(source.relative_to(ROOT))]
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    args.output.mkdir(parents=True, exist_ok=True)
    label = "axioms"
    (args.output / f"{label}.log").write_text(result.stdout)
    if result.returncode:
        raise SystemExit(f"Lean exited {result.returncode}; see {args.output}")
    reports = parse_report(result.stdout)
    missing = expected - reports.keys()
    forbidden = {name: sorted(axioms - ALLOWED) for name, axioms in reports.items() if axioms - ALLOWED}
    if missing or forbidden:
        raise SystemExit(f"Missing queries: {sorted(missing)}; forbidden axioms: {forbidden}")
    summary = {"command": command, "source": str(source.relative_to(ROOT)),
               "expected_queries": len(expected), "reported_declarations": len(reports),
               "axioms": sorted(set().union(*reports.values())), "exit": 0}
    (args.output / f"{label}.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"{label}: {len(expected)} queried declarations; only allowed axioms")


if __name__ == "__main__":
    main()
