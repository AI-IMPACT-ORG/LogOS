{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.Interpretation.Normalize where

-- Normalisation: drop vacuous quantifiers (a useful post-transformer for closure).

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  ; _<|>_
  ; Unit
  ; cmpNat
  )

open import LogOS.Apps.ZFC.Proof.Syntax using
    ( Term; Formula
    ; var; emptyT; pairT; unionT; powerT; succT; omegaT
    ; ⊥F; _∈F_; _≈F_
    ; _⇒_; _∧F_; _∨F_; _↔F_
    ; ∀F; ∃F
    ; Renaming; renameFormula
    )

usesVarTerm : ℕ → Term → Maybe Unit
usesVarTerm k (var n) with cmpNat k n
... | Core.equal = just tt
... | Core.less = nothing
... | Core.greater = nothing
usesVarTerm k emptyT = nothing
usesVarTerm k (pairT t u) = usesVarTerm k t <|> usesVarTerm k u
usesVarTerm k (unionT t) = usesVarTerm k t
usesVarTerm k (powerT t) = usesVarTerm k t
usesVarTerm k (succT t) = usesVarTerm k t
usesVarTerm k omegaT = nothing

-- Does the variable at index `k` (in the current binder context) occur free?
--
-- Under a binder, outer variables shift by +1, so we check `suc k`.
usesVarFormula : ℕ → Formula → Maybe Unit
usesVarFormula k ⊥F = nothing
usesVarFormula k (t ∈F u) = usesVarTerm k t <|> usesVarTerm k u
usesVarFormula k (t ≈F u) = usesVarTerm k t <|> usesVarTerm k u
usesVarFormula k (φ ⇒ ψ) = usesVarFormula k φ <|> usesVarFormula k ψ
usesVarFormula k (φ ∧F ψ) = usesVarFormula k φ <|> usesVarFormula k ψ
usesVarFormula k (φ ∨F ψ) = usesVarFormula k φ <|> usesVarFormula k ψ
usesVarFormula k (φ ↔F ψ) = usesVarFormula k φ <|> usesVarFormula k ψ
usesVarFormula k (∀F φ) = usesVarFormula (suc k) φ
usesVarFormula k (∃F φ) = usesVarFormula (suc k) φ

drop0Ren : Renaming
drop0Ren zero = zero
drop0Ren (suc n) = n

dropVacuousQuantifiers : Formula → Formula
dropVacuousQuantifiers ⊥F = ⊥F
dropVacuousQuantifiers (t ∈F u) = t ∈F u
dropVacuousQuantifiers (t ≈F u) = t ≈F u
dropVacuousQuantifiers (φ ⇒ ψ) = dropVacuousQuantifiers φ ⇒ dropVacuousQuantifiers ψ
dropVacuousQuantifiers (φ ∧F ψ) = dropVacuousQuantifiers φ ∧F dropVacuousQuantifiers ψ
dropVacuousQuantifiers (φ ∨F ψ) = dropVacuousQuantifiers φ ∨F dropVacuousQuantifiers ψ
dropVacuousQuantifiers (φ ↔F ψ) = dropVacuousQuantifiers φ ↔F dropVacuousQuantifiers ψ
dropVacuousQuantifiers (∀F φ) with dropVacuousQuantifiers φ
... | φ' with usesVarFormula zero φ'
... | nothing = renameFormula drop0Ren φ'
... | just _  = ∀F φ'
dropVacuousQuantifiers (∃F φ) with dropVacuousQuantifiers φ
... | φ' with usesVarFormula zero φ'
... | nothing = renameFormula drop0Ren φ'
... | just _  = ∃F φ'
