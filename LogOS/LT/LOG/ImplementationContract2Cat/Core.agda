{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.ImplementationContract2Cat.Core where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Contract-equipped kernels as a law stack over the architectural base `LOGᴳ`.
--
-- Reading:
-- - architecture: boundary morphisms + boundary-only refinements
-- - implementation: displayed code-level witnesses over that architecture
-- - law: displayed contracts layered on top of the implementation stack

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)
open import LogOS.LT.Kernel using (bnd)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Coherence using (under)

open import LogOS.LT.LOG.Boundary2Cat using
  ( LOGᴳ
  ; map∂
  ; map∂-mono
  )

import LogOS.LT.LOG.Contract2Cat as ContractLOG
import LogOS.LT.LOG.ImplementationLawStack2Cat as ImplementationLaw

ContractDisplayedᴳ
  : ∀ {ℓ ℓRel ℓCode : Level}
  → DisplayedThin2Cat (LOGᴳ {ℓ} {ℓRel} {ℓCode}) ℓ ℓRel
ContractDisplayedᴳ {ℓ} {ℓRel} {ℓCode} =
  let
    C = LOGᴳ {ℓ} {ℓRel} {ℓCode}
    module C = Thin2Cat C
  in
  record
    { Ob = λ K → Con (bnd K)
    ; HomD = λ {K} {K'} (h : Con (C.Hom K K')) c c' →
        _⊑_ (bnd K') c' (map∂ h c)
    ; idD = λ {K} c → ConPreorder.refl (bnd K)
    ; compD = λ {K₁} {K₂} {K₃} {h} {k} {c₁} {c₂} {c₃} compat₁₂ compat₂₃ →
        let
          module R = ≤-Reasoning (bnd K₃)
          open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
        in
        begin⊑
          c₃ ⊑⟨ compat₂₃ ⟩
          map∂ k c₂ ⊑⟨ map∂-mono k compat₁₂ ⟩
          map∂ k (map∂ h c₁) ∎⊑
    }

module Base {ℓ ℓRel ℓCode : Level} =
  ImplementationLaw.Build
    ContractLOG.ContractTag
    ContractLOG.contractTagId
    (ContractDisplayedᴳ {ℓ} {ℓRel} {ℓCode})
    (ContractLOG.ContractDisplayed {ℓ} {ℓRel} {ℓCode})
    (λ c → c)
    (λ _ _ compat → compat)

open Base public
  renaming
    ( lawSig to contractSig
    ; lawSingleton to contractSingleton
    ; lawStackᴳ to contractStackᴳ
    ; ImplementationLawStackLike to ImplementationContractStackLike
    ; ImplementationLawStack to ImplementationContractStack
    ; ImplementationLawStackUnder to ImplementationContractStackUnder
    ; ImplementationLawCatLike to LOGᴳʳ∂Like
    ; ImplementationLawCat to LOGᴳʳ∂
    ; ImplementationLawCatUnder to LOGᴳʳ∂⊑
    ; ImplementationLawKernel to ImplementationContractKernel
    ; lawOf to contractOf
    ; forgetImplementationLaw to forgetᴳʳ∂→∂
    )

LOGArchitectureImplementationContract = LOGᴳʳ∂
LOGArchitectureImplementationContractUnder = LOGᴳʳ∂⊑
