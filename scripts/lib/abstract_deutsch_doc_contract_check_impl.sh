#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
#
# Shared implementation for the abstract Deutsch doc contract checks.

# shellcheck shell=bash

abstract_deutsch_doc_contract_check_impl() {
  local check_name="$1"

  check_require_cmd "${check_name}" rg

  local doc="docs/Patterns/Shared_Distributed_Semantics.lagda.md"
  [[ -f "${doc}" ]] || check_die "${check_name}" "missing doc: ${doc}"

  rg -q --fixed-strings "LogOS/Ports/AbstractDeutsch2Cat.agda" "${doc}" \
    || check_die "${check_name}" "doc contract violation: ${doc} must mention LogOS/Ports/AbstractDeutsch2Cat.agda"

  rg -qi --fixed-strings "local reversibility" "${doc}" \
    || check_die "${check_name}" "doc contract violation: ${doc} must mention 'local reversibility'"

  echo "${check_name}: OK"
}
