{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Discipline.PortsAsDisplayed.ArchitectureLaws where

open import LogOS.Prelude using (lzero; ⊤; tt)

import LogOS.Ports.AbstractDeutsch2Cat.Laws

ok : ⊤ {ℓ = lzero}
ok = tt
