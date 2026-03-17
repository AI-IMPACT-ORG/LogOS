<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: first-order names and dependent payloads

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.First_Order_Names_And_Dependent_Payloads where

import LogOS.API.LT
```

Decision
--------

- If a structure needs raw lookup, leftmost shadowing, no-dup, or similar
  first-order bookkeeping, do not ask the dependent payload to serve as the
  raw identity carrier.
- Instead, split the surface into:
  - a small first-order name used by raw structural operations, and
  - a richer dependent payload packaged in an entry record.

Why this is the LogOS default
-----------------------------

- LogOS is refinement-first and equality-quarantined.
- A dependent payload such as `Tag : Set ℓ` is not, by itself, the right raw
  notion of identity for lookup under `--without-K`.
- Treating such a payload as the lookup key would force a stronger,
  equality-first identity story than the LT lane actually needs.
- The split keeps raw structure weak and explicit, while preserving precise
  dependent typing at the point where semantics is really used.

Normal form
-----------

When this pattern applies, package the surface in two layers.

- **Raw layer:** a first-order name `Name` supports membership, shadowing,
  uniqueness, and structural recursion.
- **Typed layer:** an entry record packages `Name` together with the dependent
  payload and whatever displayed structure or laws the payload determines.

Decision rule
-------------

- If the operation is about lookup order, duplicate resolution, or uniqueness:
  compare names.
- If the operation is about actual semantics, displayed structure, or
  forgetting/projection: carry the whole entry.
- Do not promote the dependent payload itself to the raw symbol unless the
  payload is already a genuinely first-order name.

Port-stack instance
-------------------

The port-stack refactor now follows this pattern explicitly.

- `PortLabel` is the first-order identity carrier.
- `PortSig C label Tag` says that the label `label` carries payload `Tag` and a
  displayed thin 2-category over `C`.
- `PortEntry C` packages the label, the payload type, and the signature.
- `Member label` is raw label-based lookup.
- `EntryMember entry` is exact typed membership for one chosen entry.
- `NoDupStack` ranges over labels, not over payload types.

Pedantic boundary
-----------------

- Two entries may share the same payload type and still be distinct entries if
  their names differ.
- Conversely, raw duplicate resolution is about equal names, not about any
  semantic equivalence between payloads.
- This is why public uniqueness surfaces now quantify over concrete entries,
  while raw no-dup hypotheses only mention labels.

Concrete code anchors
---------------------

- `LogOS/LT/Ports/PortSig.agda`
- `LogOS/LT/Ports/PortStack/Raw.agda`
- `LogOS/LT/Ports/PortStack/Unique.agda`
- `LogOS/Checks/PortStackUniqueCons.agda`
- `LogOS/Checks/Conventions/PortLabelPayloadSplit.agda`

Related note
------------

- `docs/Patterns/Ports_As_Displayed.lagda.md`
