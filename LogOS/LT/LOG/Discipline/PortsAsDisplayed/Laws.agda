{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.Discipline.PortsAsDisplayed.Laws where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude using (lzero; ⊤; tt)

import LogOS.LT.Hom.Laws
import LogOS.LT.BoundaryImplementation.Laws
import LogOS.LT.LOG.Implementation2Cat.Laws

ok : ⊤ {ℓ = lzero}
ok = tt
