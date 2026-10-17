#!/usr/bin/env python3
"""Generate the project's searchable doc-gen4 API, one module at a time.

Run after the serial proof and doc-gen4 builds. --wait-for-build also permits
generation alongside the first proof build, documenting only completed modules.
Dependency import links lead to their pinned source files; this site does not
duplicate the entire Mathlib API. No proof source or compiled artifact is edited.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import time
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / "docbuild"
BUILD = DOC / ".lake/build"
EXE = DOC / ".lake/packages/doc-gen4/.lake/build/bin/doc-gen4"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def external_sources():
    result = {}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        base = ROOT / ".lake/packages" / package["name"]
        url = package["url"].removesuffix(".git") + "/blob/" + package["rev"]
        # Lake packages used here keep their Lean source under their root.
        for source in base.rglob("*.lean"):
            relative = source.relative_to(base)
            if ".lake" not in relative.parts:
                result[str(relative.with_suffix(".html"))] = url + "/" + str(relative)
    toolchain = (ROOT / "lean-toolchain").read_text().strip().split(":")[-1]
    sysroot = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"],
                                          cwd=ROOT, text=True).strip())
    for source in (sysroot / "src/lean").rglob("*.lean"):
        relative = source.relative_to(sysroot / "src/lean")
        key = str(relative.with_suffix(".html"))
        remote = str(relative)
        if key.startswith("lake/"):
            key = key.removeprefix("lake/")
        result[key] = f"https://github.com/leanprover/lean4/blob/{toolchain}/src/{remote}"
    return result


def fix_dependency_links():
    site = BUILD / "doc"
    sources = external_sources()
    replaced = 0
    for page in site.rglob("*.html"):
        def rewrite(match):
            nonlocal replaced
            link = urlsplit(match.group(1))
            if link.scheme or link.netloc or not link.path or link.path.startswith("/"):
                return match.group(0)
            target = (page.parent / unquote(link.path)).resolve()
            if target.exists() or not target.is_relative_to(site):
                return match.group(0)
            relative = str(target.relative_to(site))
            if relative in sources:
                replaced += 1
                return 'href="' + sources[relative] + '"'
            return match.group(0)
        page.write_text(re.sub(r'href="([^"]+)"', rewrite, page.read_text()))
    return replaced


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wait-for-build", action="store_true")
    args = parser.parse_args()
    if not EXE.exists():
        raise SystemExit("Build doc-gen4 in docbuild first; see docbuild/README.md")
    paths = [p for p in git("ls-files", "*.lean").splitlines()
             if p == "MultiplicativeBasisDeformations.lean" or
             p.startswith(("MultiplicativeBasisDeformations/", "MBDVendor/"))]
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--", *paths,
                    "lean-toolchain", "lake-manifest.json", "lakefile.toml"], cwd=ROOT, check=True)
    if not args.wait_for_build:
        subprocess.run(["lake", "--no-build", "build", "MultiplicativeBasisDeformations"], cwd=ROOT, check=True)
    BUILD.mkdir(parents=True, exist_ok=True)
    state_path = BUILD / "api-build.json"
    state = json.loads(state_path.read_text()) if state_path.exists() else {
        "source_commit": git("rev-parse", "HEAD"), "modules": {}}
    # Reuse documentation only while its source revision describes these proofs.
    subprocess.run(["git", "diff", "--exit-code", state["source_commit"], "HEAD", "--",
                    *paths, "lean-toolchain", "lake-manifest.json", "lakefile.toml"], cwd=ROOT, check=True)
    env = dict(os.environ, DISABLE_EQUATIONS="1", LEAN_NUM_THREADS="1")
    def run(*command):
        subprocess.run(["lake", "env", str(EXE), *command], cwd=DOC, env=env, check=True)
    run("bibPrepass", "--build", str(BUILD), "--none")
    remaining = set(paths)
    while remaining:
        progressed = False
        for path in sorted(remaining):
            artifact = ROOT / ".lake/build/lib/lean" / Path(path).with_suffix(".olean")
            if not artifact.exists():
                continue
            stamp = artifact.stat().st_mtime_ns
            module = path.removesuffix(".lean").replace("/", ".")
            if state["modules"].get(module) != stamp:
                print(f"[{len(paths) - len(remaining) + 1}/{len(paths)}] {module}", flush=True)
                source = ("https://github.com/haruhisa-enomoto/multiplicative-bases-deformations/blob/"
                          + state["source_commit"] + "/" + path)
                run("single", "--build", str(BUILD), module, "api-docs.db", source)
                state["modules"][module] = stamp
                state_path.write_text(json.dumps(state, indent=2) + "\n")
            remaining.remove(path)
            progressed = True
        if remaining and not progressed:
            if not args.wait_for_build:
                raise SystemExit(f"Missing {len(remaining)} compiled modules; finish the proof build")
            print(f"Waiting for {len(remaining)} modules from the proof build", flush=True)
            time.sleep(10)
    # Omitting roots renders exactly the project modules inserted in this DB.
    run("fromDb", "--build", str(BUILD), "--manifest", str(BUILD / "api-manifest.json"),
        str(BUILD / "api-docs.db"))
    state["dependency_source_links"] = fix_dependency_links()
    state["complete"] = True
    state_path.write_text(json.dumps(state, indent=2) + "\n")
    print(f"Generated API for {len(paths)} modules at {BUILD / 'doc'}", flush=True)


if __name__ == "__main__":
    main()
