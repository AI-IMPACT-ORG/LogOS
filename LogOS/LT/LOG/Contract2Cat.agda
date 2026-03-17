{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.Contract2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Contract-equipped kernels as a thin 2-category (LOG∂).
-- (A Σ-decoration (Grothendieck-style; refinement inherited from the base) of a displayed structure over `LOG`.)
--
-- Objects: contracts `mkContract K c` where `c : Con (bnd K)`
-- 1-cells: kernel morphisms h : K → K' equipped with the contract law
--          c' ⊑ map∂ h c
-- 2-cells: inherited boundary-driven observational refinements (`_⇒∂_`) on the underlying kernel morphisms

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.Kernel using (Kernel; bnd)
open import LogOS.LT.Hom.Core using (KernelHom; map∂; map∂-mono)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)
open import LogOS.LT.Contracts using (ContractLaw)
import LogOS.LT.Contracts as Contracts

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.Template.Singleton2Cat as Template

data ContractTag : Set where
  contractTag : ContractTag

contractTagId : ℕ
contractTagId = 21

-- Displayed contracts over kernels.
ContractDisplayed
  : ∀ {ℓ ℓRel ℓCode : Level}
  → DisplayedThin2Cat (LOG {ℓ} {ℓRel} {ℓCode}) ℓ ℓRel
ContractDisplayed {ℓ} {ℓRel} {ℓCode} =
  record
    { Ob = λ K → Con (bnd K)
    ; HomD = λ {K} {K'} (h : KernelHom K K') c c' →
        ContractLaw {ℓCode = ℓCode} (Contracts.mkContract K c) (Contracts.mkContract K' c') h
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

module Port {ℓ ℓRel ℓCode : Level} =
  Template.SingletonLayer
    contractTagId
    {Tag = ContractTag}
    (ContractDisplayed {ℓ} {ℓRel} {ℓCode})

contractSig
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortSig.PortSig (LOG {ℓ} {ℓRel} {ℓCode}) contractTagId ContractTag
contractSig {ℓ} {ℓRel} {ℓCode} =
  Port.portSig {ℓ} {ℓRel} {ℓCode}

open Port public using (port2Cat; singleton; stack; Displayed; WithPort; forget; port)
