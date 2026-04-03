#!/bin/zsh

set -euo pipefail

repo_root="${1:-$(cd "$(dirname "$0")/.." && pwd)}"
run_build="${RUN_BUILD:-0}"

failures=0

print_section() {
  printf '\n== %s ==\n' "$1"
}

record_success() {
  printf '[ok] %s\n' "$1"
}

record_failure() {
  printf '[fail] %s\n' "$1"
  failures=$((failures + 1))
}

run_check() {
  local label="$1"
  shift
  if "$@" >/tmp/hlm_check_stdout.$$ 2>/tmp/hlm_check_stderr.$$; then
    record_success "$label"
    sed -n '1,10p' /tmp/hlm_check_stdout.$$
  else
    record_failure "$label"
    sed -n '1,20p' /tmp/hlm_check_stderr.$$ >&2
    sed -n '1,20p' /tmp/hlm_check_stdout.$$ >&2
  fi
  rm -f /tmp/hlm_check_stdout.$$ /tmp/hlm_check_stderr.$$
}

print_section "Repository"
printf 'root: %s\n' "$repo_root"

print_section "Locality"

dataless_count="$(
  cd "$repo_root" &&
  find . -flags +dataless -type f 2>/dev/null | wc -l | tr -d ' '
)"

printf 'dataless files: %s\n' "$dataless_count"
if [[ "$dataless_count" == "0" ]]; then
  record_success "all files are materialized locally"
else
  record_failure "repository still contains dataless files"
fi

for target in README.md .git/HEAD .git/config HigherLambdaModel.lean; do
  if [[ -e "$repo_root/$target" ]]; then
    flags="$(stat -f '%Sf' "$repo_root/$target" 2>/dev/null || true)"
    printf '%s flags=%s\n' "$target" "$flags"
  else
    record_failure "missing expected file: $target"
  fi
done

if [[ -e "$repo_root/paper/manuscript.tex" ]]; then
  flags="$(stat -f '%Sf' "$repo_root/paper/manuscript.tex" 2>/dev/null || true)"
  printf '%s flags=%s\n' "paper/manuscript.tex" "$flags"
elif [[ -e "$repo_root/paper/K_infinity_homotopy_lambda_model.pdf" ]]; then
  flags="$(stat -f '%Sf' "$repo_root/paper/K_infinity_homotopy_lambda_model.pdf" 2>/dev/null || true)"
  printf '%s flags=%s\n' "paper/K_infinity_homotopy_lambda_model.pdf" "$flags"
else
  record_failure "missing expected paper artifact"
fi

print_section "Read checks"
run_check "read README.md" zsh -lc "cd '$repo_root' && head -n 5 README.md"
run_check "read .git/HEAD" zsh -lc "cd '$repo_root' && head -n 5 .git/HEAD"

print_section "Git"
run_check "git rev-parse --show-toplevel" zsh -lc "cd '$repo_root' && git rev-parse --show-toplevel"

print_section "Lean"
run_check "lean --version" zsh -lc "cd '$repo_root' && lean --version"

if [[ "$run_build" == "1" ]]; then
  print_section "Build"
  run_check "lake build" zsh -lc "cd '$repo_root' && lake build"
else
  print_section "Build"
  printf 'skipped: set RUN_BUILD=1 to include `lake build`\n'
fi

print_section "Summary"
if [[ "$failures" == "0" ]]; then
  printf 'Repository is ready for formalization work.\n'
else
  printf 'Repository is not ready. failures=%s\n' "$failures"
  exit 1
fi
