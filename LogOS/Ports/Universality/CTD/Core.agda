{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.CTD.Core where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (_⊑_)
open import LogOS.LT.Flow using (GuardedClosure; Flow)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode)
open import LogOS.LT.Hom.Core using (KernelHom)
open import LogOS.LT.HomFlow using (KernelHomFlow)

import LogOS.LT.Hom.Core as Hom
import LogOS.LT.Theorems.Effectivisation as Eff

record FlowSimulationFamily {ℓ ℓRel ℓCode ℓSys : Level}
  : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode ⊔ ℓSys)) where
  field
    Sys : Set ℓSys
    K   : Sys → Kernel ℓ ℓRel ℓCode
    GC  : (s : Sys) → GuardedClosure (bnd (K s))
    U   : Kernel ℓ ℓRel ℓCode
    GCᵁ : GuardedClosure (bnd U)
    simulate
      : (s : Sys)
      → Σ
          (KernelHom (K s) U)
          (λ h → KernelHomFlow (GC s) GCᵁ h)

  sim : (s : Sys) → KernelHom (K s) U
  sim s = proj₁ (simulate s)

  simFlow : (s : Sys) → KernelHomFlow (GC s) GCᵁ (sim s)
  simFlow s = proj₂ (simulate s)

  normalize-simulate
    : ∀ (s : Sys) (γ : Code (K s))
    → _⊑_ (bnd U)
        (Hom.map∂ (sim s) (Flow (GC s) (decode (K s) γ)))
        (Flow GCᵁ (decode U (Hom.mapCode (sim s) γ)))
  normalize-simulate s γ =
    Eff.normalize-decode-mapCode {K = K s} {K' = U}
      (GC s) GCᵁ (sim s) (simFlow s) γ

open FlowSimulationFamily public
