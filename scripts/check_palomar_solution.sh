#!/usr/bin/env bash
# Local existing-artifact Solution/Comparator replay only, NOT Palomar preflight
# or submission, a clean build, or a transitive source-import audit.
# Adapted from the reference scripts/check_palomar_prototype.sh.
# Never fetch, resolve dependencies, or build the production proof closure here.
set -euo pipefail
if (( $# > 1 )) || [[ ${1:-} != '' && ${1:-} != --comparator ]]; then
  printf 'Usage: bash scripts/check_palomar_solution.sh [--comparator]\n' >&2
  exit 2
fi
mode=${1:-}
repository=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repository"
tools=$(dirname "$(readlink -f "$(elan which lean)")")
mkdir -p .lake/audit/palomar-solution
outputs=$(mktemp -d "$repository/.lake/audit/palomar-solution/run.XXXXXX")
printf 'Local replay outputs (not a Palomar submission): %s\n' "$outputs"
mkdir -p "$outputs/challenge/Palomar" "$outputs/solution/Palomar" \
  "$outputs/solution/Tests" "$outputs/control/Tests" "$outputs/tmp"
sha256sum Palomar/Challenge.lean Palomar/Solution.lean \
  Tests/SolutionAxioms.lean Tests/WrongStatement.lean comparator.json \
  scripts/check_palomar_solution.sh scripts/extract_proof_sources.py \
  source-manifests/production.json source-manifests/repairs.json \
  lean-toolchain lakefile.toml lake-manifest.json > "$outputs/SOURCE-SHA256SUMS"
git rev-parse HEAD > "$outputs/base-commit.txt"

# Fail closed on unsupported manifest entries; read only existing pinned builds.
jq -e 'any(.packages[]; .name == "mathlib" and
  .url == "https://github.com/leanprover-community/mathlib4")' \
  lake-manifest.json > /dev/null
jq -er '.packages[] | if .type != "git" then error("git dependency required")
  else [(.name | ltrimstr("«") | rtrimstr("»")), .rev] | @tsv end' \
  lake-manifest.json > "$outputs/dependency-pins.tsv"
dependency_path=""
dependency_binds=()
while IFS=$'\t' read -r package revision; do
  [[ $package =~ ^[A-Za-z_][A-Za-z0-9_-]*$ && $revision =~ ^[0-9a-f]{40}$ ]]
  package_root=$(readlink -f ".lake/packages/$package")
  [[ $(git -C "$package_root" rev-parse HEAD) == "$revision" ]]
  git -C "$package_root" diff --quiet HEAD --
  [[ -d "$package_root/.lake/build/lib/lean" ]]
  printf '%s %s\n' "$package" "$revision" >> "$outputs/dependencies.txt"
  dependency_path+="$package_root/.lake/build/lib/lean:"
  dependency_binds+=(--ro-bind "$package_root" "$package_root")
done < "$outputs/dependency-pins.tsv"
dependency_path+="$tools/../lib/lean"
[[ -d "$repository/.lake/build/lib/lean" ]]

# Header-only direct whitelist: no compiler resolution or transitive audit claim.
PYTHONDONTWRITEBYTECODE=1 python3 - > "$outputs/challenge-direct-imports.json" <<'PY'
import json
from pathlib import Path
import sys
sys.path.insert(0, str(Path("scripts").resolve()))
from extract_proof_sources import parse_header

allowed = {
    "Mathlib.ModelTheory.Semantics",
    "Mathlib.SetTheory.Cardinal.Aleph",
    "Mathlib.Topology.Constructions",
    "Mathlib.Topology.Order",
    "Mathlib.Topology.Perfect",
}
header = parse_header(Path("Palomar/Challenge.lean").read_text(encoding="utf-8"))
if not header.module or header.prelude:
    raise SystemExit("Challenge requires its reviewed module header and implicit Init")
for item in header.imports:
    if item.module not in allowed or not item.public or item.meta or item.all:
        raise SystemExit(f"Unsupported Challenge direct import: {item.manifest()}")
print(json.dumps({
    "scope": "explicit direct header imports only; NOT a transitive audit",
    "implicit_import": "Init",
    "imports": [item.manifest() for item in header.imports],
}, sort_keys=True, indent=2))
PY

sandbox=(/usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user
  --tmpfs /tmp --dev /dev --proc /proc --clearenv --unshare-all
  --die-with-parent --new-session --ro-bind "$(dirname "$tools")" "$(dirname "$tools")"
  --ro-bind "$repository" "$repository" "${dependency_binds[@]}"
  --setenv PATH "$tools:/usr/bin:/bin" --chdir "$repository")
compile() {
  local module=$1 build=$2 relative
  relative=${module//./\/}
  shift 2
  "${sandbox[@]}" --bind "$build" "$build" \
    --setenv LEAN_PATH "$build:$repository/.lake/build/lib/lean:$dependency_path" -- \
    "$tools/lean" -R . -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -Dbackward.privateInPublic=false -Dlinter.deprecated=false -Dlinter.all=false "$@" \
    -o "$build/$relative.olean" "$relative.lean"
}
# Match the reviewed package's lint settings; proof/axiom/kernel checks stay strict.
# Challenge alone permits its reviewed theorem hole; this is not a hole-location audit.
# SolutionAxioms checks the solution and both bridges against the three standard axioms.
compile Palomar.Challenge "$outputs/challenge" > "$outputs/challenge.log" 2>&1
compile Palomar.Solution "$outputs/solution" -DwarningAsError=true > "$outputs/solution.log" 2>&1
compile Tests.SolutionAxioms "$outputs/solution" -DwarningAsError=true > "$outputs/audit.log" 2>&1
compile Tests.WrongStatement "$outputs/control" -DwarningAsError=true > "$outputs/control.log" 2>&1
if [[ "$mode" == --comparator ]]; then
  target=PalomarChallenge.independent_challenge
  primitives=(propext Quot.sound Classical.choice
    Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble
    Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight
    String.ofList Char.ofNat List eagerReduce Nat String String.mk Char
    optParam autoParam semiOutParam outParam Quot Quot.mk Quot.lift Quot.ind)
  export_module() {
    local module=$1 build=$2
    "${sandbox[@]}" \
      --setenv LEAN_PATH "$build:$repository/.lake/build/lib/lean:$dependency_path" -- \
      "$tools/leanexport" "$module" -- "$target" "${primitives[@]}"
  }
  export_module Palomar.Challenge "$outputs/challenge" > "$outputs/challenge.ndjson"
  export_module Palomar.Solution "$outputs/solution" > "$outputs/solution.ndjson"
  export_module Tests.WrongStatement "$outputs/control" > "$outputs/wrong.ndjson"
  compare() {
    COMPARATOR_BWRAP=/usr/bin/bwrap PATH="$tools:/usr/bin:/bin" TMPDIR="$outputs/tmp" \
      "$tools/lake" comparator --config "$repository/comparator.json" \
      --challenge-from-export "$outputs/challenge.ndjson" --solution-from-export "$1"
  }
  reject() {
    local input=$1 log=$2 diagnostic=$3 status=0
    compare "$input" > "$log" 2>&1 || status=$?
    [[ "$status" == 1 ]]
    grep -Fq "$diagnostic" "$log"
  }
  reject "$outputs/wrong.ndjson" "$outputs/wrong.log" \
    "Challenge and solution theorem statement do not match: '$target'"
  reject "$outputs/challenge.ndjson" "$outputs/challenge-as-proof.log" \
    "Illegal axiom detected: 'sorryAx'"
  compare "$outputs/solution.ndjson" 2>&1 | tee "$outputs/comparator.log"
  grep -Fq 'nanoda kernel accepts the solution' "$outputs/comparator.log"
  grep -Fq 'Lean default kernel accepts the solution' "$outputs/comparator.log"
  sha256sum "$outputs/"*.ndjson > "$outputs/EXPORT-SHA256SUMS"
fi
sha256sum --check --status "$outputs/SOURCE-SHA256SUMS"
printf 'Local existing-artifact checks passed; NOT Palomar submission, clean build, or transitive import audit: %s\n' "$outputs"
