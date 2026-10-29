#!/usr/bin/env bash
# shellcheck shell=bash

# Pinned external toolchain/repository versions for reproducible builds.

readonly NODE_MAJOR_VERSION_LOCKED="22"
readonly EMSDK_VERSION_LOCKED="4.0.21"

readonly MOX_REPO_LOCKED="https://github.com/normal-computing/mox.git"
readonly MOX_REF_LOCKED="b90b3a51a68b772a1510c837166afd6d429d8f20"
readonly MOX_LLVM_SUBMODULE_REF_LOCKED="e3e4f161d0160f10dc7cbd746abd639dd740ecde"

# Mirrored from gitlab.com/surfer-project/surfer pages_build (main pipeline
# 2625476633, job 15008633862, commit 98287107b9, 2026-06-24). We host our own
# copy because GitLab only keeps the *latest* pipeline's artifacts, so the
# upstream "latest main" URL is a moving target that breaks the pinned SHA, and
# job-ID URLs 404 once the artifacts expire. To refresh: download the new
# pages_build zip, upload it to the 'surfer-web' release, and update both lines.
readonly SURFER_ARTIFACT_URL_LOCKED="https://github.com/thomasnormal/sv-tutorial/releases/download/surfer-web/surfer-pages_build.zip"
readonly SURFER_ARTIFACT_SHA256_LOCKED="8ab484d373120ac3a49592ebe87eaa8a9dc22714eb6c9dded0de495314a1df44"
