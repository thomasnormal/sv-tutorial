#!/usr/bin/env bash
# shellcheck shell=bash

# Pinned external toolchain/repository versions for reproducible builds.

readonly NODE_MAJOR_VERSION_LOCKED="22"
readonly EMSDK_VERSION_LOCKED="4.0.21"

readonly MOX_REPO_LOCKED="https://github.com/normal-computing/mox.git"
readonly MOX_REF_LOCKED="e5e0f6b2898a4b3f1763916077504a7d15e730b1"
readonly MOX_LLVM_SUBMODULE_REF_LOCKED="aa3d6b37c7945bfb4c261dd994689de2a2de25bf"

readonly SURFER_ARTIFACT_URL_LOCKED="https://gitlab.com/surfer-project/surfer/-/jobs/artifacts/main/download?job=pages_build"
readonly SURFER_ARTIFACT_SHA256_LOCKED="abf8d4c3415d445bf86edb39dda9ec9f37d20ccddf4069ec925acb608dcb661b"
