{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.TypeTheory.Core where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Shallow “type theory” aliases over the LT kernel/hom surface.
--
-- This is a view layer only:
-- - no new judgements,
-- - no new equalities,
-- - no new axioms.

open import LogOS.Prelude
open import LogOS.LT.Coherence using (CohMode)
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.Kernel using (Kernel; bnd)
import LogOS.LT.Hom.Core as Hom
import LogOS.LT.Contracts as Contracts

Ty : (ℓ ℓRel ℓCode : Level) → Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
Ty = Kernel

Tm
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ : Level}
  → (m : CohMode)
  → Kernel ℓ ℓRel ℓCode₁
  → Kernel ℓ ℓRel ℓCode₂
  → Set _
Tm m = Hom.KernelHomLike m

Prop : ∀ {ℓ ℓRel ℓCode : Level} → Ty ℓ ℓRel ℓCode → Set ℓ
Prop K = Con (bnd K)

id
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
    {A : Ty ℓ ℓRel ℓCode}
  → Tm m A A
id {m} {A = A} = Hom.idKernelHomLike {m = m} A

infixr 40 _∘_
_∘_
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {A : Ty ℓ ℓRel ℓCode₁}
    {B : Ty ℓ ℓRel ℓCode₂}
    {C : Ty ℓ ℓRel ℓCode₃}
  → Tm m B C
  → Tm m A B
  → Tm m A C
_∘_ {m = m} = Hom._∘Like_ {m = m}

Contract : ∀ {ℓ ℓRel ℓCode : Level} → Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
Contract {ℓ} {ℓRel} {ℓCode} = Contracts.Contract {ℓ} {ℓRel} {ℓCode}

contract
  : ∀ {ℓ ℓRel ℓCode : Level}
  → (K : Ty ℓ ℓRel ℓCode)
  → Prop K
  → Contract {ℓ} {ℓRel} {ℓCode}
contract K c = Contracts.mkContract K c
