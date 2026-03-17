<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Summit pack

This pack is an apps-side capstone surface over theorem families that already live in
the LT layer, the ports layer, and existing app metatheory.

It does not define a new foundational doctrine.

Implemented now

- conservative recognition of mechanisable fragments via `GeneralisationPolicy`
- strong downstream mechanisability as one apps-side adjective
  (`MechanisableDownstream`)
- optional summit-side admissibility via `ObservationalSufficiency`
  (“No Ghost In The Machine”), yielding no-backflow of visible collapse into the
  recognised seed image
- local shared-boundary symmetry via
  `symmetryRespecting→noForkOnImage` and
  `symmetryRespecting→weakTerminalOnImage`
- package-level local symmetry via
  `summitPackage→noForkOnImage`,
  `summitPackage→weakTerminalOnImage`, and
  `summitPackages→sameImagePresentation`, now read over one recognised image and one
  fixed mechanisable payload
- quantitative capstone packaging via `QuantitativeSummit`
- diagonal obstruction packaging via `MechanisabilityObstruction`
- direct downstream-facing consequence functions via `mechanisableRecognition`,
  `mechanisableQuantitative`, `mechanisableObstruction`, and
  `mechanisablePayloadOnImage`
- one constructor from bare conservative generalisation via
  `atLeastAsStrongAsMechanisable→mechanisable`

Entrypoints

- `LogOS/Apps/Summit/Policy.agda`
- `LogOS/Apps/Summit/Recognition.agda`
- `LogOS/Apps/Summit/Mechanisable.agda`
- `LogOS/Apps/Summit/Admissibility.agda`
- `LogOS/Apps/Summit/Quantitative.agda`
- `LogOS/Apps/Summit/Obstruction.agda`
- `LogOS/Apps/Summit/Theorem.agda`
- `docs/Results/Summit.lagda.md`
