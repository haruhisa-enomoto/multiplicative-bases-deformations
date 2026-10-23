# API documentation

This separate project pins doc-gen4 to its Lean 4.35.0-rc3 release, so that
documentation dependencies do not enter the proof package's dependency list.

After building the root package, build doc-gen4 here and generate the API:

```sh
cd docbuild
lake build doc-gen4
cd ..
python3 scripts/build_api.py
python3 scripts/build_website.py
python3 scripts/check_website.py
```

The generator documents every library module, using doc-gen4's SQLite
database and HTML/search renderer. It links dependency imports to their exact
source revisions instead of regenerating Mathlib's documentation.

Generated API pages are copied into `_site/api/`. The API records its source
commit in `.lake/build/api-build.json`; after Lean sources change, remove the
ignored documentation build directory and regenerate.
