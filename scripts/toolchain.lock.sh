#!/usr/bin/env bash
# shellcheck shell=bash

# Pinned external toolchain/repository versions for reproducible builds.

readonly NODE_MAJOR_VERSION_LOCKED="22"
readonly EMSDK_VERSION_LOCKED="4.0.21"

readonly CIRCT_REPO_LOCKED="https://github.com/thomasnormal/circt.git"
readonly CIRCT_REF_LOCKED="6334424eee194b21b9b33148742071e8201fbbc2"
readonly CIRCT_LLVM_SUBMODULE_REF_LOCKED="972cd847efb20661ea7ee8982dd19730aa040c75"

readonly SURFER_ARTIFACT_URL_LOCKED="https://gitlab.com/surfer-project/surfer/-/jobs/artifacts/main/download?job=pages_build"
readonly SURFER_ARTIFACT_SHA256_LOCKED="a8eba2eba26d6a2bc34dd6c347b65ebbc10acbfbb31769f2bf091f4f97f01814"
