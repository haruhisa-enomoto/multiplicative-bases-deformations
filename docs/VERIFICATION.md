# Verification

The library proves Theorems A and B and every numbered result of the October
17, 2026 manuscript with mathematical content; the
[correspondence](PAPER-CORRESPONDENCE.md) lists the declarations. Records are
in [`verification/`](../verification/).

## Independent statement

`MultiplicativeBasisDeformations/Statement.lean` states both theorems with
Mathlib alone: complete families of finite-dimensional indecomposable right
modules, the Jacobson radical and normed multiplicative bases, basic algebras,
the radical of the category of indecomposable modules, the Auslander–Reiten
quiver with arrows indexed by bases of `J/J²`, almost split sequences, and the
mesh category as the linear path category modulo the sums of all paths
`τX → Y → X`.

`Statement.theoremA` and `Statement.theoremB` prove these statements from the
library. The bridge shows:

* an independent family is a skeleton of the library with the same radical
  powers and spaces of irreducible maps;
* the translate defined by almost split sequences is the translation of the
  library, defined from the vendored minimal right almost split maps
  (`Statement.translateCompatible`);
* the mesh coefficients from almost split sequences normalize to one
  (Lemma 4.4), so the independent mesh category is equivalent to the one used
  by the library.

`Challenge.lean` is generated from `Statement.lean` with two deliberate
`sorry` placeholders, for Theorems A and B. `Solution.lean` proves them and
does not import the Challenge.

## Results of October 17, 2026

| Check | Result |
| --- | --- |
| Fresh library build (no project artifacts, Mathlib from cache) | 9254 jobs, 21 min 54 s, peak 8.7 GB, research commit `36f7a0d57` |
| Library build after adding the independent statement | 9261 jobs, no `sorry` |
| Axiom audit, `scripts/AxiomAudit.lean` and the independent theorems | only `propext`, `Classical.choice`, `Quot.sound` |
| Comparator replay of Challenge and Solution | statement match, axiom boundary, NanoDa and Lean kernel replay passed; 7 min 36 s, peak 7.4 GB |

The [Comparator record](../verification/2026-10-17/comparator.json) gives the
Challenge and Solution hashes and tool pins. The replay reused tool builds made
for the magnitude-conjecture repository with the same pins; the exporter is
the v4.33.0 source compiled with Lean 4.33.1. This is a local replay, not a
hosted Palomar preflight or registry acceptance.

## Reproduce the checks

```sh
lake exe cache get
lake build
python3 scripts/audit_axioms.py
python3 scripts/generate_challenge.py --check
lake build Challenge Solution
./scripts/verify-comparator.sh
```

`verify-comparator.sh` clones and builds Comparator, lean4export, NanoDa and
Landrun at these commits, and needs Go and Rust:

| Tool | Source commit |
| --- | --- |
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

Use a machine with at least 16 GB of memory.

## Website and API

```sh
cd docbuild && lake build doc-gen4 && cd ..
python3 scripts/build_api.py
python3 scripts/build_website.py
python3 scripts/check_website.py
python3 -m http.server 8000 --directory _site --bind 127.0.0.1
```
