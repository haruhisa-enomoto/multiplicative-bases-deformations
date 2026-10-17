#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cache_root=${PALOMAR_COMPARATOR_CACHE:-"$repository_root/.cache/palomar-comparator"}
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"

comparator_commit=575674928e239f5bc452aab72d1dd7b0f1326494
lean4export_commit=15f6055e299ad5b89345e533cc2192f4cc00f659
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

for required_command in cargo git go lake python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run Comparator" >&2
    exit 1
  fi
done

python3 - "$repository_root/comparator.json" <<'PY'
import json
import pathlib
import sys

config_path = pathlib.Path(sys.argv[1])
try:
    config = json.loads(config_path.read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {config_path}: {error}", file=sys.stderr)
    raise SystemExit(1)

if not isinstance(config, dict) or config.get("enable_nanoda") is not True:
    print(
        f"error: {config_path}: enable_nanoda must be exactly true; "
        "the NanoDa replay is required",
        file=sys.stderr,
    )
    raise SystemExit(1)
PY

mkdir -p "$cache_root" "$bin_dir"

checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none "$repository" "$destination"
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"

if [ ! -f "$lean4export_dir/lean-toolchain" ]; then
  echo "error: pinned lean4export revision $lean4export_commit has no lean-toolchain file" >&2
  echo "select a lean4export revision that declares its Lean toolchain" >&2
  exit 1
fi

project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
lean4export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
# PalomarSubmission 3561d237 accepts the same-release-line patch-zero
# exporter source, rebuilt with the project's exact patch toolchain.
# The project pin is unchanged; this is the resolver-selected exporter.
if [ "$project_toolchain" != "$lean4export_toolchain" ]; then
  if [ "$project_toolchain" != "leanprover/lean4:v4.33.1" ] ||
     [ "$lean4export_toolchain" != "leanprover/lean4:v4.33.0" ]; then
    echo "error: unsupported exporter/project toolchain combination" >&2
    exit 1
  fi
  echo "Using v4.33.0 exporter source with the v4.33.1 compiler; see docs/VERIFICATION.md"
fi

checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"

GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"

python3 "$repository_root/scripts/build_lean_serial.py" \
  --package "$comparator_dir" --output "$repository_root/.build-audit/comparator-tool" \
  --max-rss-kib 12582912 comparator
ELAN_TOOLCHAIN="$project_toolchain" python3 "$repository_root/scripts/build_lean_serial.py" \
  --package "$lean4export_dir" --output "$repository_root/.build-audit/exporter-tool" \
  --max-rss-kib 12582912 lean4export
(cd "$nanoda_dir" && cargo build --release --locked)

cd "$repository_root"
python3 scripts/generate_challenge.py --check
PALOMAR_LANDRUN_BIN="$bin_dir/landrun" \
COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
COMPARATOR_LANDRUN="$repository_root/scripts/landrun-wrapper.sh" \
  lake env "$comparator_dir/.lake/build/bin/comparator" comparator.json
