#!/usr/bin/env bash
# Build a reusable sectioned MOX package artifact.
#
# The frontend owns the artifact format; this wrapper deliberately has no
# package-name or UVM logic. Give it a package source file and include root,
# then publish the resulting .vlib beside the Mox build that produced it.
set -euo pipefail

usage() {
  cat >&2 <<'EOF'
Usage: scripts/build-package-artifact.sh --mox-verilog PATH --source PACKAGE.sv \
  --include-dir DIR --output PATH [--name NAME] [--mode mapped|lowered]

The output is a sectioned .vlib containing package IR. Mapped artifacts are
consumed with --read-vlib OUTPUT --read-vlib-mapped-moore-ir; lowered-library
artifacts use --read-vlib OUTPUT --read-vlib-lowered-library-ir.
EOF
  exit 2
}

mox_verilog=''
source_file=''
include_dir=''
output=''
name='package'
mode='mapped'
while (($#)); do
  case "$1" in
    --mox-verilog) mox_verilog=${2:?missing value for --mox-verilog}; shift 2 ;;
    --source) source_file=${2:?missing value for --source}; shift 2 ;;
    --include-dir) include_dir=${2:?missing value for --include-dir}; shift 2 ;;
    --output) output=${2:?missing value for --output}; shift 2 ;;
    --name) name=${2:?missing value for --name}; shift 2 ;;
    --mode) mode=${2:?missing value for --mode}; shift 2 ;;
    -h|--help) usage ;;
    *) echo "unknown argument: $1" >&2; usage ;;
  esac
done

[[ -x "$mox_verilog" ]] || { echo "mox-verilog is not executable: $mox_verilog" >&2; exit 1; }
[[ -f "$source_file" ]] || { echo "package source is missing: $source_file" >&2; exit 1; }
[[ -d "$include_dir" ]] || { echo "include directory is missing: $include_dir" >&2; exit 1; }
[[ -n "$output" ]] || { echo "--output is required" >&2; exit 2; }
case "$mode" in
  mapped) ir_flag='--ir-moore'; write_flag='--write-vlib-mapped-moore-ir' ;;
  lowered) ir_flag='--ir-llhd'; write_flag='--write-vlib-lowered-library-ir' ;;
  *) echo "--mode must be mapped or lowered: $mode" >&2; exit 2 ;;
esac

mkdir -p "$(dirname "$output")"
"$mox_verilog" \
  "$ir_flag" \
  --single-unit \
  --write-vlib-format=sectioned \
  "$write_flag" \
  --write-vlib "$output" \
  -I "$include_dir" \
  "$source_file" \
  -o /dev/null

echo "Built $name package artifact: $output"
stat -c 'bytes=%s' "$output"
sha256sum "$output"
