{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.Fidelity where

-- Fidelity is the spec/obs reading of the same two-view agreement structure.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
import LogOS.Ports.Universality.Agreement as Agreement

FidelityPort
  : ∀ {ℓCode ℓSpecCon ℓSpecRel ℓObsCon ℓObsRel : Level}
  → (CodeType : Set ℓCode)
  → (Spec : ConPreorder ℓSpecCon ℓSpecRel)
  → (Obs : ConPreorder ℓObsCon ℓObsRel)
  → Set (lsuc (ℓCode ⊔ ℓSpecCon ⊔ ℓSpecRel ⊔ ℓObsCon ⊔ ℓObsRel))
FidelityPort = Agreement.AgreementPort

FidelityAgreement
  : ∀ {ℓCode ℓCon ℓRel : Level}
  → {CodeType : Set ℓCode}
  → {CP : ConPreorder ℓCon ℓRel}
  → FidelityPort CodeType CP CP
  → Set (lsuc (ℓCode ⊔ ℓCon ⊔ ℓRel))
FidelityAgreement = Agreement.AgreementContract
