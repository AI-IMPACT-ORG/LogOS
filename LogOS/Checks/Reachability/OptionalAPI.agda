{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Reachability.OptionalAPI where

-- Policy-only reachability root for curated API modules that are intentionally
-- kept off the default `LogOS.API.LT` surface.
-- Architecture is no longer listed here: the tetrahedron package is part of
-- the default curated LT surface.

import LogOS.API.Minimal
import LogOS.API.Views
import LogOS.API.Valuation
import LogOS.API.Opacity
import LogOS.API.Reification
import LogOS.API.Ports.Dependent
import LogOS.API.Ports.Universality
import LogOS.Prelude.Fin
import LogOS.Prelude.Fin.Cardinality
import LogOS.Prelude.FiniteFamily
