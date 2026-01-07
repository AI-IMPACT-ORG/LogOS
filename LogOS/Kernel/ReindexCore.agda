{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.ReindexCore where

-- ============================================================================
-- SHARED SIGNATURE REINDEXING CORE (WORLD + KERNEL SHAPE)
--
-- Both `Kernel` and `LogicKernel` support pullback along `SigHom` by:
-- - reindexing worlds/satisfaction (S/H tiers) contravariantly, and
-- - preserving constraints and code on-the-nose.
--
-- This module factors out the shared construction at the level of `KernelShape`.
-- ============================================================================

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop
open import LogOS.Kernel.Core as Core

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

-- Reindex a kernel shape along a signature map.
--
-- Note: This is the lightweight signature morphism story: it preserves formulas,
-- constraints, and code, and only reindexes the observation/world indices.

reindexKernelShape
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    → SigHom Sig₁ Sig₂
    → Core.KernelShape Sig₂ Q
    → Core.KernelShape Sig₁ Q
reindexKernelShape {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Q = Q} σ S₂ =
  record
    { HWorld = WH₁
    ; BB     = Core.KernelShape.BB S₂
    ; MBulk  = Core.KernelShape.MBulk S₂
    ; MBnd   = Core.KernelShape.MBnd S₂
    ; Holo   = Core.KernelShape.Holo S₂

    ; HTruth = record
        { Sat_H = λ w c →
            HT₂.HLayer.Sat_H (Core.KernelShape.HTruth S₂) (SigHom.mapCosp σ w) c
        ; mono-Con = λ {w} {c} {c'} c≤c' sat →
            HT₂.HLayer.mono-Con (Core.KernelShape.HTruth S₂) c≤c' sat
        ; mono-ctx = λ {w} {w'} {c} w≤w' sat →
            HT₂.HLayer.mono-ctx (Core.KernelShape.HTruth S₂) w≤w' sat
        }

    ; HInv = record
        { Inv_H     = HT₂.Invariance.Inv_H (Core.KernelShape.HInv S₂)
        ; infl      = HT₂.Invariance.infl (Core.KernelShape.HInv S₂)
        ; idemp-lax = HT₂.Invariance.idemp-lax (Core.KernelShape.HInv S₂)
        }

    ; Sat_H_bnd = λ w c → Core.KernelShape.Sat_H_bnd S₂ (SigHom.map∂Cosp σ w) c
    ; sat-coh   = λ w c →
        let
          coh₂ = Core.KernelShape.sat-coh S₂ (SigHom.mapCosp σ w) c
          eq   = SigHom.to∂-pres σ w
        in
        Prop.intro
          (λ satH →
            subst (λ x → Core.KernelShape.Sat_H_bnd S₂ x c) (sym eq)
              (Prop.to coh₂ satH))
          (λ satB →
            Prop.from coh₂
              (subst (λ x → Core.KernelShape.Sat_H_bnd S₂ x c) eq satB))

    ; Fml    = Core.KernelShape.Fml S₂
    ; Strict = record
        { Sat_S = λ w φ →
            ST₂.StrictLayer.Sat_S (Core.KernelShape.Strict S₂) (SigHom.mapCosp σ w) φ
        }
    ; TransH = Core.KernelShape.TransH S₂
    ; coh-LH = λ w φ → Core.KernelShape.coh-LH S₂ (SigHom.mapCosp σ w) φ

    ; Code          = Core.KernelShape.Code S₂
    ; encode        = Core.KernelShape.encode S₂
    ; decode        = Core.KernelShape.decode S₂
    ; decode∘encode = Core.KernelShape.decode∘encode S₂
    ; Guard         = Core.KernelShape.Guard S₂
    ; Body          = Core.KernelShape.Body S₂
    ; γ*            = Core.KernelShape.γ* S₂
    ; γ*-guard      = Core.KernelShape.γ*-guard S₂
    ; reify         = Core.KernelShape.reify S₂
    ; reify-decode  = Core.KernelShape.reify-decode S₂
    ; Body∂         = Core.KernelShape.Body∂ S₂
    ; body-decode   = Core.KernelShape.body-decode S₂
    }
  where
    WH₁ : Worlds.WorldH Sig₁ Q
    WH₁ = reindexWorldH σ (Core.KernelShape.HWorld S₂)

    module HT₂ = Truth.HomotypicalTruth Sig₂ Q (Core.KernelShape.HWorld S₂)
    module ST₂ = Truth.StrictTruth Sig₂
