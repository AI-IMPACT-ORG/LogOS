<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Deep Dive — PL Mechanization Spine (FOL + While)

```agda
{-# OPTIONS --safe #-}
module docs.DeepDive.PLSpine where

-- Sync guard: this module is a checked “pointer” to the small mechanization
-- spine used by several narratives (syntax/statics/dynamics).
import docs.DeepDive.PLSpineSpine as Spine

open Spine public
```

This page is intentionally small: it just anchors the minimal mechanization
spine in `docs/DeepDive/PLSpineSpine.agda` so docs CI keeps it in sync.
