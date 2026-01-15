<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Legacy surfaces

This page collects legacy packaging modules that are kept for reference but are
not part of the curated surfaces. They are intentionally isolated and should
not be imported by pack entrypoints.

The aggregated, legacy-only entrypoint is:
- `LogOS/Domain/Legacy/All.agda`

## Complexity

- `LogOS/Domain/Legacy/Complexity/PvsNP.agda`
  - Packaging-only PvsNP wrapper (assumptions = claim).

## Opacity

- `LogOS/Domain/Legacy/Opacity/AccessibleWeilLimitBridge.agda`
  - Superseded by the meet-limit + stable/cofinal bridge.
- `LogOS/Domain/Legacy/Opacity/AccessibleWeilMeetLimitBridge.agda`
  - Direct meet-limit bridge without stable/cofinal refinements.
- `LogOS/Domain/Legacy/Opacity/ZetaAccessibleMeetLimitLedger.agda`
  - Superseded by the stable meet-limit ledger.
