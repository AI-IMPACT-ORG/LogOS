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
            HLayer.Sat_H (Core.KernelShape.HTruth S₂) (SigHom.mapCosp σ w) c
        ; mono-Con = λ {w} {c} {c'} c≤c' sat →
            HLayer.mono-Con (Core.KernelShape.HTruth S₂) c≤c' sat
        ; mono-ctx = λ {w} {w'} {c} w≤w' sat →
            HLayer.mono-ctx (Core.KernelShape.HTruth S₂) w≤w' sat
        }

    ; HInv = record
        { Inv_H     = Invariance.Inv_H (Core.KernelShape.HInv S₂)
        ; infl      = Invariance.infl (Core.KernelShape.HInv S₂)
        ; idemp-lax = Invariance.idemp-lax (Core.KernelShape.HInv S₂)
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
            StrictLayer.Sat_S (Core.KernelShape.Strict S₂) (SigHom.mapCosp σ w) φ
        }
    ; TransH = Core.KernelShape.TransH S₂
    ; coh-LH = λ w φ → Core.KernelShape.coh-LH S₂ (SigHom.mapCosp σ w) φ

    ; Code          = Core.KernelShape.Code S₂
    ; encode        = Core.KernelShape.encode S₂
    ; decode        = Core.KernelShape.decode S₂
    ; Guard         = Core.KernelShape.Guard S₂
    ; Body          = Core.KernelShape.Body S₂
    ; γ*            = Core.KernelShape.γ* S₂
    ; reify         = Core.KernelShape.reify S₂
    ; Body∂         = Core.KernelShape.Body∂ S₂
    }
  where
    WH₁ : Worlds.WorldH Sig₁ Q
    WH₁ = reindexWorldH σ (Core.KernelShape.HWorld S₂)

    module HT₂ = Truth.HomotypicalTruth Sig₂ Q (Core.KernelShape.HWorld S₂)
    open HT₂
    module ST₂ = Truth.StrictTruth Sig₂
    open ST₂

-- Reindex a kernel shape along a signature map, while translating formulas.
--
-- This adds an explicit sentence-translation layer (Σ-morphism on syntax) on top
-- of the world reindexing: formulas are mapped into the target kernel’s syntax
-- and then interpreted there. Constraints and code stay on-the-nose.

reindexKernelShapeWithFml
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (S₂ : Core.KernelShape Sig₂ Q)
    {Fml₁ : Set ℓ}
  → (Fml₁ → Core.KernelShape.Fml S₂)
  → Core.KernelShape Sig₁ Q
reindexKernelShapeWithFml {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Q = Q} σ S₂ {Fml₁} mapFml =
  let
    S = reindexKernelShape σ S₂
    module ST₂ = Truth.StrictTruth Sig₂
  in
  record
    { HWorld = Core.KernelShape.HWorld S
    ; BB     = Core.KernelShape.BB S
    ; MBulk  = Core.KernelShape.MBulk S
    ; MBnd   = Core.KernelShape.MBnd S
    ; Holo   = Core.KernelShape.Holo S

    ; HTruth = Core.KernelShape.HTruth S
    ; HInv   = Core.KernelShape.HInv S

    ; Sat_H_bnd = Core.KernelShape.Sat_H_bnd S
    ; sat-coh   = Core.KernelShape.sat-coh S

    ; Fml    = Fml₁
    ; Strict = record
        { Sat_S = λ w φ →
            ST₂.StrictLayer.Sat_S (Core.KernelShape.Strict S₂) (SigHom.mapCosp σ w) (mapFml φ)
        }
    ; TransH = λ φ → Core.KernelShape.TransH S₂ (mapFml φ)
    ; coh-LH = λ w φ → Core.KernelShape.coh-LH S₂ (SigHom.mapCosp σ w) (mapFml φ)

    ; Code          = Core.KernelShape.Code S
    ; encode        = Core.KernelShape.encode S
    ; decode        = Core.KernelShape.decode S
    ; Guard         = Core.KernelShape.Guard S
    ; Body          = Core.KernelShape.Body S
    ; γ*            = Core.KernelShape.γ* S
    ; reify         = Core.KernelShape.reify S
    ; Body∂         = Core.KernelShape.Body∂ S
    }

reindexKernelShapeLaws
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (S₂ : Core.KernelShape Sig₂ Q)
  → Core.KernelShapeLaws S₂
  → Core.KernelShapeLaws (reindexKernelShape σ S₂)
reindexKernelShapeLaws σ S₂ laws₂ =
  let open Core.KernelShapeLaws laws₂ renaming
        ( decode∘encode to decode∘encode₂
        ; γ*-guard to γ*-guard₂
        ; reify-decode to reify-decode₂
        ; body-decode to body-decode₂
        )
  in record
    { decode∘encode = decode∘encode₂
    ; γ*-guard      = γ*-guard₂
    ; reify-decode  = reify-decode₂
    ; body-decode   = body-decode₂
    }

reindexKernelShapeLawsWithFml
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (S₂ : Core.KernelShape Sig₂ Q)
    {Fml₁ : Set ℓ}
  → (mapFml : Fml₁ → Core.KernelShape.Fml S₂)
  → Core.KernelShapeLaws S₂
  → Core.KernelShapeLaws (reindexKernelShapeWithFml σ S₂ mapFml)
reindexKernelShapeLawsWithFml σ S₂ _ laws₂ =
  let open Core.KernelShapeLaws laws₂ renaming
        ( decode∘encode to decode∘encode₂
        ; γ*-guard to γ*-guard₂
        ; reify-decode to reify-decode₂
        ; body-decode to body-decode₂
        )
  in record
    { decode∘encode = decode∘encode₂
    ; γ*-guard      = γ*-guard₂
    ; reify-decode  = reify-decode₂
    ; body-decode   = body-decode₂
    }

reindexKernelLaws
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (S₂ : Core.KernelShape Sig₂ Q)
    (G  : Truth.GuardedCore.GuardedClosure (BulkBoundary.bnd (Core.KernelShape.BB S₂)))
  → Core.KernelLaws S₂ G
  → Core.KernelLaws (reindexKernelShape σ S₂) G
reindexKernelLaws σ S₂ G laws₂ =
  let open Core.KernelLaws laws₂ renaming
        ( shapeLaws to shapeLaws₂
        ; mono-Body∂ to mono-Body∂₂
        ; mono-Flow to mono-Flow₂
        ; guard-decode to guard-decode₂
        ; decode-γ* to decode-γ*₂
        )
  in record
    { shapeLaws    = reindexKernelShapeLaws σ S₂ shapeLaws₂
    ; mono-Body∂    = mono-Body∂₂
    ; mono-Flow     = mono-Flow₂
    ; guard-decode  = guard-decode₂
    ; decode-γ*     = decode-γ*₂
    }

reindexKernelLawsWithFml
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (S₂ : Core.KernelShape Sig₂ Q)
    (G  : Truth.GuardedCore.GuardedClosure (BulkBoundary.bnd (Core.KernelShape.BB S₂)))
    {Fml₁ : Set ℓ}
  → (mapFml : Fml₁ → Core.KernelShape.Fml S₂)
  → Core.KernelLaws S₂ G
  → Core.KernelLaws (reindexKernelShapeWithFml σ S₂ mapFml) G
reindexKernelLawsWithFml σ S₂ G mapFml laws₂ =
  let open Core.KernelLaws laws₂ renaming
        ( shapeLaws to shapeLaws₂
        ; mono-Body∂ to mono-Body∂₂
        ; mono-Flow to mono-Flow₂
        ; guard-decode to guard-decode₂
        ; decode-γ* to decode-γ*₂
        )
  in record
    { shapeLaws    = reindexKernelShapeLawsWithFml σ S₂ mapFml shapeLaws₂
    ; mono-Body∂    = mono-Body∂₂
    ; mono-Flow     = mono-Flow₂
    ; guard-decode  = guard-decode₂
    ; decode-γ*     = decode-γ*₂
    }
