<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Agda allowlists policy

In LogOS, allowlists are **quarantines**: they are permitted only to document *explicit exceptions* to otherwise-hard
rules, and they must stay small, justified, and non-stale.

The source of truth is the executable policy in `scripts/check/*_check.sh` (see `docs/Generated/Policy_Index.md`).

## Non-negotiables

- Prefer fixing the underlying violation over allowlisting it.
- Every allowlist entry must be justified in the allowlist file (comment immediately above the entry, or an inline
  comment where the corresponding checker permits it).
- An entry must be **unique** (no duplicates) and **non-stale** (it must correspond to a real, current exception).
- No entry may be active in multiple allowlists (overlap is rejected by `scripts/check/stale_allowlists_check.sh` where
  applicable).

## Allowlist categories

### `scripts/postulate_allowlist.txt` (postulate quarantine)

Purpose: allow `postulate` in specific files only.

Rules:

- `postulate` is forbidden by default (`scripts/check/postulate_policy_check.sh`).
- Each entry is a repo-relative file path.
- Every allowlisted file that contains `postulate` must include a structured justification block
  (`POSTULATE-JUSTIFICATION` + required fields), as enforced by `scripts/check/postulate_policy_check.sh`.
- Entries must be justified, unique, and non-stale (`scripts/check/stale_allowlists_check.sh`).

### `scripts/layer_order_allowlist.txt` (must stay empty)

Purpose: (theoretical) quarantine for layering violations.

Policy: this allowlist must stay empty; layering violations must be fixed in code, not quarantined.

Enforced by: `scripts/check/layer_order_check.sh` + `scripts/check/stale_allowlists_check.sh`.

### `scripts/policy_coverage_allowlist.txt` (must stay empty)

Purpose: (theoretical) emergency escape hatch while wiring new `scripts/check/*_check.sh` into CI.

Policy: this allowlist must stay empty; every `scripts/check/*_check.sh` must be runnable as a `make <check>` target and be
wired into `make ci-policy`.

Enforced by: `scripts/check/policy_coverage_check.sh` + `scripts/check/stale_allowlists_check.sh`.

### `scripts/root_hygiene_allowlist.txt` (root-level `*.agda` exceptions)

Purpose: allow specific root-level `*.agda` files (top of repo).

Policy:

- Prefer moving code under `LogOS/**` or `docs/**` rather than adding root-level modules.
- Keep this list minimal and add a justification comment for every entry (even if not machine-enforced).

Enforced by: `scripts/check/root_hygiene_check.sh`.

## Procedure

1. Add the minimal allowlist entry with a justification comment.
2. Make the exception mechanically honest (e.g. if you allowlist a postulate-bearing file, add the required
   justification block).
3. Run `make ci-policy` (or at least `make stale-allowlists-check` plus the relevant policy check).
