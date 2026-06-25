#!/usr/bin/env bash
# shellcheck shell=bash

# Pinned external toolchain/repository versions for reproducible builds.

readonly NODE_MAJOR_VERSION_LOCKED="22"
readonly EMSDK_VERSION_LOCKED="4.0.21"

readonly MOX_REPO_LOCKED="https://github.com/normal-computing/mox.git"
readonly MOX_REF_LOCKED="805b42d2d2a95c98e954bddd2071bd52f1ced0b4"
readonly MOX_LLVM_SUBMODULE_REF_LOCKED="aa3d6b37c7945bfb4c261dd994689de2a2de25bf"

# Mirrored from gitlab.com/surfer-project/surfer pages_build (main pipeline
# 2625476633, job 15008633862, commit 98287107b9, 2026-06-24). We host our own
# copy because GitLab only keeps the *latest* pipeline's artifacts, so the
# upstream "latest main" URL is a moving target that breaks the pinned SHA, and
# job-ID URLs 404 once the artifacts expire. To refresh: download the new
# pages_build zip, upload it to the 'surfer-web' release, and update both lines.
readonly SURFER_ARTIFACT_URL_LOCKED="https://github.com/thomasnormal/sv-tutorial/releases/download/surfer-web/surfer-pages_build.zip"
readonly SURFER_ARTIFACT_SHA256_LOCKED="8ab484d373120ac3a49592ebe87eaa8a9dc22714eb6c9dded0de495314a1df44"
