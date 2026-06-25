#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT_DIR/scripts/toolchain.lock.sh"

MOX_REPO="${MOX_REPO:-$MOX_REPO_LOCKED}"
MOX_REF="${MOX_REF:-$MOX_REF_LOCKED}"
MOX_LLVM_SUBMODULE_REF="${MOX_LLVM_SUBMODULE_REF:-$MOX_LLVM_SUBMODULE_REF_LOCKED}"
TARGET_DIR="${1:-vendor/mox}"
ALLOW_DIRTY="${ALLOW_DIRTY:-0}"

require_clean_worktree() {
  local repo_dir="$1"
  if [[ "$ALLOW_DIRTY" == "1" ]]; then
    return 0
  fi
  if [[ -n "$(git -C "$repo_dir" status --porcelain)" ]]; then
    echo "Refusing to update dirty checkout: $repo_dir" >&2
    echo "Set ALLOW_DIRTY=1 to override." >&2
    exit 1
  fi
}

if [ -d "$TARGET_DIR/.git" ]; then
  echo "Updating existing MOX checkout in $TARGET_DIR"
  require_clean_worktree "$TARGET_DIR"
  git -C "$TARGET_DIR" remote set-url origin "$MOX_REPO"
  # Skip --tags here: the upstream fork carries many third-party tags
  # (sifive/*, firtool-*, ESIRuntime-*, llvm/*) that frequently conflict
  # with what's already local. Branches are enough to resolve $MOX_REF.
  git -C "$TARGET_DIR" fetch origin
else
  echo "Cloning MOX from $MOX_REPO into $TARGET_DIR"
  git clone "$MOX_REPO" "$TARGET_DIR"
fi

git -C "$TARGET_DIR" fetch origin "$MOX_REF"

# If the previous HEAD had llvm/uvm-core as submodules but the target ref
# stores them as committed trees, deinit the affected submodules first so
# `git checkout` can replace the gitlink with the tree files cleanly.
if git -C "$TARGET_DIR" rev-parse --verify -q HEAD >/dev/null; then
  prev_ref="$(git -C "$TARGET_DIR" rev-parse HEAD)"
  for sm_path in llvm lib/Runtime/uvm-core; do
    prev_mode="$(git -C "$TARGET_DIR" ls-tree "$prev_ref" "$sm_path" 2>/dev/null | awk '{print $1}')"
    new_mode="$(git -C "$TARGET_DIR" ls-tree "$MOX_REF" "$sm_path" 2>/dev/null | awk '{print $1}')"
    if [[ "$prev_mode" == "160000" && "$new_mode" == "040000" ]]; then
      echo "Transitioning $sm_path from submodule to tree; deiniting first."
      git -C "$TARGET_DIR" submodule deinit -f "$sm_path" 2>&1 | sed 's/^/  /' || true
    fi
  done
fi

git -C "$TARGET_DIR" checkout --detach "$MOX_REF"

# Recent commits on the upstream main branch committed the llvm and
# uvm-core sources directly into the tree instead of leaving them as
# submodule gitlinks. Detect which layout this ref uses before running
# any submodule commands.
llvm_mode="$(git -C "$TARGET_DIR" ls-tree HEAD llvm | awk '{print $1}')"

if [[ "$llvm_mode" == "160000" ]]; then
  # Submodule layout: sync and check out llvm + uvm-core as gitlinks.
  git -C "$TARGET_DIR" submodule sync --recursive
  git -C "$TARGET_DIR" submodule update --init --recursive --checkout

  if [ -n "$MOX_LLVM_SUBMODULE_REF" ]; then
    actual_llvm_ref="$(git -C "$TARGET_DIR/llvm" rev-parse HEAD)"
    if [[ "$actual_llvm_ref" != "$MOX_LLVM_SUBMODULE_REF" ]]; then
      echo "LLVM submodule ref mismatch in $TARGET_DIR/llvm" >&2
      echo "Expected: $MOX_LLVM_SUBMODULE_REF" >&2
      echo "Actual:   $actual_llvm_ref" >&2
      exit 1
    fi
  fi
elif [[ "$llvm_mode" == "040000" ]]; then
  # Tree layout: llvm sources are committed directly. Init only any
  # submodules that still exist as gitlinks at this ref.
  remaining_submodules=()
  while IFS= read -r path; do
    [ -n "$path" ] && remaining_submodules+=("$path")
  done < <(git -C "$TARGET_DIR" ls-tree -r HEAD | awk '$2=="commit" {print $4}')

  if [ "${#remaining_submodules[@]}" -gt 0 ]; then
    git -C "$TARGET_DIR" submodule sync --recursive
    git -C "$TARGET_DIR" submodule update --init --recursive --checkout \
      "${remaining_submodules[@]}"
  fi

  if [ -n "$MOX_LLVM_SUBMODULE_REF" ]; then
    echo "Note: llvm is committed as a tree at $MOX_REF; ignoring MOX_LLVM_SUBMODULE_REF override." >&2
  fi
else
  echo "Unexpected llvm tree mode at $MOX_REF: ${llvm_mode:-<missing>}" >&2
  exit 1
fi

if [[ "$llvm_mode" == "160000" ]]; then
  llvm_ref_msg="$MOX_LLVM_SUBMODULE_REF"
else
  llvm_ref_msg="(committed in tree at this ref)"
fi

cat <<MSG

MOX checkout is ready.
Pinned repo: $MOX_REPO
Pinned ref:  $MOX_REF
LLVM ref:    $llvm_ref_msg

Next:
1. Build wasm artifacts from the checkout.
   Standard tools (mox-verilog, mox-sim, mox-bmc):
     cmake ... -DMOX_SIM_WASM=ON -DMOX_BMC_WASM=ON
   VPI-capable sim for cocotb lessons (additional build target):
     cmake ... -DMOX_SIM_WASM_VPI=ON
2. Run npm run local-publish:mox (or publish:mox to also push to GitHub Release).
   (The script also patches browser-compatibility issues in mox-sim.js.)
3. Optionally override artifact URLs with VITE_* env vars in .env:
   VITE_MOX_VERILOG_JS_URL / VITE_MOX_VERILOG_WASM_URL
   VITE_MOX_SIM_JS_URL / VITE_MOX_SIM_WASM_URL
   VITE_MOX_BMC_JS_URL / VITE_MOX_BMC_WASM_URL
   VITE_MOX_SIM_VPI_JS_URL / VITE_MOX_SIM_VPI_WASM_URL

MSG
