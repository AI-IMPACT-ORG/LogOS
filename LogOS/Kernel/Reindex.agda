{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Reindex where

-- ============================================================================
-- KERNEL REINDEXING (PULLBACK) ALONG SIGNATURE MORPHISMS
--
-- Given a structure-preserving signature map `σ : SigHom Sig₁ Sig₂`, we can
-- pull back any `Kernel Sig₂ Q` to a `Kernel Sig₁ Q` by precomposing all
-- world- and satisfaction-indexed fields along `σ`.
--
-- This is designed to be *non-breaking*: it adds reindexing as a new feature
-- without changing the existing `Kernel` record or any existing models.
-- ============================================================================

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop
open import LogOS.Kernel

-- Reindex an H-world along a signature map (precompose on the Cosp carrier).

reindexWorldH
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    → SigHom Sig₁ Sig₂
    → Worlds.WorldH Sig₂ Q
    → Worlds.WorldH Sig₁ Q
reindexWorldH σ WH₂ = record
  { _≤ctx_ = λ w w' → Worlds.WorldH._≤ctx_ WH₂ (SigHom.mapCosp σ w) (SigHom.mapCosp σ w')
  ; WFlow = λ w w' → Worlds.WorldH.WFlow WH₂ (SigHom.mapCosp σ w) (SigHom.mapCosp σ w')
  ; wflow-refl = λ w → Worlds.WorldH.wflow-refl WH₂ (SigHom.mapCosp σ w)
  ; wflow-trans = λ w w' w'' →
      Worlds.WorldH.wflow-trans WH₂
        (SigHom.mapCosp σ w)
        (SigHom.mapCosp σ w')
        (SigHom.mapCosp σ w'')
  }

-- Reindex a kernel along a signature map.
--
-- Note: This is a lightweight signature morphism story: it preserves formulas,
-- constraints, and code, and only reindexes the observation/world indices.

reindexKernel
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    → SigHom Sig₁ Sig₂
    → Kernel Sig₂ Q
    → Kernel Sig₁ Q
reindexKernel {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Q = Q} σ K₂ =
  record
    { HWorld = WH₁
    ; BB     = Kernel.BB K₂
    ; MBulk  = Kernel.MBulk K₂
    ; MBnd   = Kernel.MBnd K₂
    ; Holo   = Kernel.Holo K₂

    ; HTruth = record
        { Sat_H = λ w c → HT₂.HLayer.Sat_H (Kernel.HTruth K₂) (SigHom.mapCosp σ w) c
        ; mono-Con = λ {w} {c} {c'} c≤c' sat →
            HT₂.HLayer.mono-Con (Kernel.HTruth K₂) c≤c' sat
        ; mono-ctx = λ {w} {w'} {c} w≤w' sat →
            HT₂.HLayer.mono-ctx (Kernel.HTruth K₂) w≤w' sat
        }

    ; HInv = record
        { Inv_H     = HT₂.Invariance.Inv_H (Kernel.HInv K₂)
        ; infl      = HT₂.Invariance.infl (Kernel.HInv K₂)
        ; idemp-lax = HT₂.Invariance.idemp-lax (Kernel.HInv K₂)
        }

    ; Sat_H_bnd = λ w c → Kernel.Sat_H_bnd K₂ (SigHom.map∂Cosp σ w) c
    ; sat-coh   = λ w c →
        let coh₂ = Kernel.sat-coh K₂ (SigHom.mapCosp σ w) c
            eq   = SigHom.bnd-pres σ w
        in Prop.intro
             (λ satH →
               subst (λ x → Kernel.Sat_H_bnd K₂ x c) (sym eq)
                     (Prop.to coh₂ satH))
             (λ satB →
               Prop.from coh₂
                 (subst (λ x → Kernel.Sat_H_bnd K₂ x c) eq satB))

    ; Fml    = Kernel.Fml K₂
    ; Strict = record
        { Sat_S = λ w φ →
            ST₂.StrictLayer.Sat_S (Kernel.Strict K₂) (SigHom.mapCosp σ w) φ
        ; _⊢S_ = ST₂.StrictLayer._⊢S_ (Kernel.Strict K₂)
        }
    ; TransH = Kernel.TransH K₂
    ; coh-LH = λ w φ → Kernel.coh-LH K₂ (SigHom.mapCosp σ w) φ

    ; GTruth = record
        { Flow      = GT₂.GuardedClosure.Flow (Kernel.GTruth K₂)
        ; mono      = GT₂.GuardedClosure.mono (Kernel.GTruth K₂)
        ; infl      = GT₂.GuardedClosure.infl (Kernel.GTruth K₂)
        ; idemp-lax = GT₂.GuardedClosure.idemp-lax (Kernel.GTruth K₂)
        ; Th*       = GT₂.GuardedClosure.Th* (Kernel.GTruth K₂)
        ; Th*-fixed = GT₂.GuardedClosure.Th*-fixed (Kernel.GTruth K₂)
        }

    ; Code           = Kernel.Code K₂
    ; encode         = Kernel.encode K₂
    ; decode         = Kernel.decode K₂
    ; decode∘encode  = Kernel.decode∘encode K₂
    ; Guard          = Kernel.Guard K₂
    ; Body           = Kernel.Body K₂
    ; guard-decode   = Kernel.guard-decode K₂
    ; γ*             = Kernel.γ* K₂
    ; γ*-guard       = Kernel.γ*-guard K₂
    ; decode-γ*      = Kernel.decode-γ* K₂
    ; reify          = Kernel.reify K₂
    ; reify-decode   = Kernel.reify-decode K₂
    ; Body∂          = Kernel.Body∂ K₂
    ; body-decode    = Kernel.body-decode K₂
    }
  where
    WH₁ : Worlds.WorldH Sig₁ Q
    WH₁ = reindexWorldH σ (Kernel.HWorld K₂)

    module HT₂ = Truth.HomotypicalTruth Sig₂ Q (Kernel.HWorld K₂)
    module ST₂ = Truth.StrictTruth Sig₂
    module GT₂ = Truth.GuardedTruth Sig₂ Q
