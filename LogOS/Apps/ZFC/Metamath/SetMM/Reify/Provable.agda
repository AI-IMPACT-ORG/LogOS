{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.SetMM.Reify.Provable where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Sig using (Sig; tc⊢)
open import LogOS.Apps.ZFC.Metamath.SetMM.Syntax using (PFormula)
open import LogOS.Apps.ZFC.Metamath.SetMM.Reify.WffReify using (reifyWff)

reify⊢ : Sig → (free : List ℕ) → PFormula → Maybe (List ℕ)
reify⊢ S free φ with reifyWff S free φ
... | just xs = just (tc⊢ S ∷ xs)
... | nothing = nothing
