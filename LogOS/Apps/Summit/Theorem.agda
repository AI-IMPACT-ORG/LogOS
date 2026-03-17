{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Summit.Theorem where

-- Thin umbrella module for the summit image and package theorem surfaces.
--
-- Hygiene note: apps-side modules may not public re-export whole submodules,
-- so the concrete theorem surfaces live in `Image.agda` and `Package.agda`.
-- This file intentionally remains a narrative/umbrella anchor. The actual
-- local summit theorems vary only in shared-boundary presentation data; the
-- payload is fixed downstream in the package layer.

import LogOS.Apps.Summit.Image
import LogOS.Apps.Summit.Package
