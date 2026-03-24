{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.PortStack.RawDefinitional where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Bookkeeping equalities for the explicit raw/shadowing stack lane.
--
-- The structural stack refactor moved public uniqueness away from raw
-- first-order exclusion proofs and toward exact-entry capabilities plus an
-- explicit certification token. Equality-valued bookkeeping remains quarantined
-- here.

open import LogOS.Prelude

ok : ⊤ {ℓ = lzero}
ok = tt
