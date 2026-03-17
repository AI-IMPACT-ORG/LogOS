{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.Discipline.PortsAsDisplayed where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude using (lzero; ⊤; tt)

import LogOS.LT.LOG.Implementation2Cat
import LogOS.LT.LOG.ImplementationContract2Cat
import LogOS.LT.LOG.ImplementationDecode2Cat
import LogOS.LT.LOG.ImplementationFlow2Cat
import LogOS.LT.LOG.Discipline.PortsAsDisplayed.Definitional
import LogOS.LT.LOG.Discipline.PortsAsDisplayed.Coverage

ok : ⊤ {ℓ = lzero}
ok = tt
