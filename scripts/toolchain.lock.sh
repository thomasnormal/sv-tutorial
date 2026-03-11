#!/usr/bin/env bash
# shellcheck shell=bash

# Pinned external toolchain/repository versions for reproducible builds.

readonly NODE_MAJOR_VERSION_LOCKED="22"
readonly EMSDK_VERSION_LOCKED="4.0.21"

readonly CIRCT_REPO_LOCKED="https://github.com/thomasnormal/circt.git"
readonly CIRCT_REF_LOCKED="a10b92ffd771fd458184278d26f6b980f71aa970"
readonly CIRCT_LLVM_SUBMODULE_REF_LOCKED="aa3d6b37c7945bfb4c261dd994689de2a2de25bf"

readonly SURFER_ARTIFACT_URL_LOCKED="https://gitlab.com/surfer-project/surfer/-/jobs/artifacts/main/download?job=pages_build"
readonly SURFER_ARTIFACT_SHA256_LOCKED="abf8d4c3415d445bf86edb39dda9ec9f37d20ccddf4069ec925acb608dcb661b"
