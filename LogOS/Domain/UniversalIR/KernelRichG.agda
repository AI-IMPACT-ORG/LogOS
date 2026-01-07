{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.KernelRichG where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Core using (UCode; UM; stepU; simulate)
open import LogOS.Domain.UniversalIR.Core.Minsky using (mkM)
open import LogOS.Domain.UniversalIR.IR using (lowerToIR)
import LogOS.QAdapters.QNatTop as QTop
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.ScaleOps using (ScaleOps)
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Graded
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Ordinal as Ord using (Ord; fin; ω)
open import Data.List using ([])

-- Graded kernel over UniversalIR UCode with decode = id.
-- The boundary order is trivial, so any flow is admissible; grades are
-- operationalized via finite-step simulation. The saturation grade `ω` is
-- interpreted as the canonical “lower to IR” closure (`lowerToIR`).

Sig : LogOSSignature lzero
Sig = record
  { sorts = record { Iface = ⊤ ; Cosp = ⊤ ; ∂Cosp = ⊤ }
  ; cospanOps = record
      { src = λ _ → tt ; tgt = λ _ → tt ; idC = λ _ → tt ; _∘C_ = λ _ _ → tt
      ; _⊕C_ = λ _ _ → tt ; _⊗C_ = λ _ _ → tt
      }
  ; boundaryOps = record
      { src∂ = λ _ → tt ; tgt∂ = λ _ → tt ; id∂ = λ _ → tt ; _∘∂_ = λ _ _ → tt
      ; _⊕∂_ = λ _ _ → tt ; _⊗∂_ = λ _ _ → tt ; from∂ = λ _ → tt ; to∂ = λ _ → tt
      }
  }

Q : QAdapter lzero
Q = QTop.QNatTop

Ops : ScaleOps Q
Ops = QTop.scaleOps

module W = Worlds Sig

HWorld : W.WorldH Q
HWorld = record
  { _≤ctx_ = λ _ _ → ⊤
  ; WFlow = λ _ _ → QAdapter.e Q
  ; wflow-refl = λ _ → QAdapter.≤s-refl Q
  ; wflow-trans = λ _ _ _ → QAdapter.≤s-refl Q
  }

conPosetU : ConPoset lzero
conPosetU = record { Con = UCode ; _⊑_ = λ _ _ → ⊤ ; refl = tt ; trans = λ _ _ → tt }

BB : BulkBoundary lzero
BB = record { bulk = conPosetU ; bnd = conPosetU }

MBulk : MonoidalPoset (BulkBoundary.bulk BB)
MBulk = record { _⊗_ = λ x _ → x ; I = UM (mkM 0 0 0 0 0 []) ; mono⊗ = λ _ _ → tt }

MBnd : MonoidalPoset (BulkBoundary.bnd BB)
MBnd = record { _⊗_ = λ x _ → x ; I = UM (mkM 0 0 0 0 0 []) ; mono⊗ = λ _ _ → tt }

Holo : LaxMonoidalAdjunction BB MBulk MBnd
Holo = record
  { core = record
      { ext = λ x → x ; bnd = λ x → x ; unit-lax = λ _ → tt ; counit-lax = λ _ → tt
      }
  ; ext-⊗-lax = λ _ _ → tt ; ext-I-lax = tt ; bnd-⊗-lax = λ _ _ → tt ; bnd-I-lax = tt
  }

module HT = Truth.HomotypicalTruth Sig Q HWorld

HTruth : HT.HLayer BB
HTruth = record { Sat_H = λ _ _ → ⊤ ; mono-Con = λ _ _ → tt ; mono-ctx = λ _ _ → tt }

HInv : HT.Invariance BB
HInv = record { Inv_H = λ c → c ; infl = λ _ → tt ; idemp-lax = λ _ → tt }

module GT = Truth.GuardedCore {ℓ = lzero}

GTruth : GT.GradedClosure Q (BulkBoundary.bnd BB)
GTruth = record
  { Flow       = λ where
      (fin n) c → simulate n c
      ω       c → lowerToIR c
  ; mono       = λ {g} _ → tt
  ; mono-grade = λ _ _ → tt
  ; comp-lax   = λ _ _ _ → tt
  ; sat        = ω
  ; sat-top    = λ { (fin _) → tt ; ω → tt }
  ; infl-sat   = λ _ → tt
  ; idemp-sat  = λ _ → tt
  ; Th*        = UM (mkM 0 0 0 0 0 [])
  ; Th*-fixed  = (tt , tt)
  }

GUKR : GradedKernel Sig Q
GUKR = record
  { shape = record
      { HWorld = HWorld
      ; BB     = BB
      ; MBulk  = MBulk
      ; MBnd   = MBnd
      ; Holo   = Holo
      ; HTruth = HTruth
      ; HInv   = HInv
      ; Sat_H_bnd = λ _ _ → ⊤
      ; sat-coh   = λ _ _ → record { to = λ _ → tt ; from = λ _ → tt }
      ; Fml    = ⊤
      ; Strict = record { Sat_S = λ _ _ → ⊤ }
      ; TransH = λ _ → UM (mkM 0 0 0 0 0 [])
      ; coh-LH = λ _ _ → record { to = λ _ → tt ; from = λ _ → tt }
      ; Code   = UCode
      ; encode = λ γ → γ
      ; decode = λ γ → γ
      ; decode∘encode = λ _ → refl
      ; Guard  = stepU
      ; Body   = λ γ → γ
      ; γ*     = UM (mkM 0 0 0 0 0 [])
      ; γ*-guard = (tt , tt)
      ; reify  = λ γ → γ
      ; reify-decode = λ _ → refl
      ; Body∂  = λ c → c
      ; body-decode = λ _ → refl
      }
  ; GTruth = GTruth
  ; step-grade = fin (suc zero)
  ; guard-decode = λ _ → refl
  ; decode-γ* = refl
  }
