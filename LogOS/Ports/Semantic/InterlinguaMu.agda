{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.InterlinguaMu where

-- μ-level transport/naturality for canonical translations between presentations.
--
-- This module connects two existing pieces of the library:
-- - Interlingua (ports/presentations) gives step-level commutation of `Extend`.
-- - μ-fusion gives limit-level transport for Kleene μ on ωCPO preorders.
--
-- The goal is to make “stabilisation is presentation independent” stateable as
-- a theorem, with explicit ωCPO/continuity hypotheses, rather than as folklore.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Minimal.Con using (ConPreorder; MonoOn)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Ports.Semantic.PresentationCore using (SatSystem; satSystem; PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor)
import LogOS.Ports.Semantic.HeteroInterlinguaCore as Hetero

import LogOS.Minimal.MuFusion as MuFusion

module For
  {ℓCtx₁ ℓCon₁ ℓForm₁ ℓSat₁ : Level}
  {Ctx₁ : Set ℓCtx₁}
  (CP₁ : ConPreorder ℓCon₁)
  {Sat₁ : Ctx₁ → ConPreorder.Con CP₁ → Set ℓSat₁}
  {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
  {Ctx₂ : Set ℓCtx₂}
  (CP₂ : ConPreorder ℓCon₂)
  {Sat₂ : Ctx₂ → ConPreorder.Con CP₂ → Set ℓSat₂}
  (m  : SatMor
          (satSystem Ctx₁ (ConPreorder.Con CP₁) Sat₁)
          (satSystem Ctx₂ (ConPreorder.Con CP₂) Sat₂))
  (P₁ : PresentationC {ℓForm = ℓForm₁}
          (satSystem Ctx₁ (ConPreorder.Con CP₁) Sat₁))
  (P₂ : PresentationC {ℓForm = ℓForm₂}
          (satSystem Ctx₂ (ConPreorder.Con CP₂) Sat₂))
  where

  private
    Con₁ = ConPreorder.Con CP₁
    Con₂ = ConPreorder.Con CP₂

    module CP₁ = ConPreorder CP₁ renaming (_⊑_ to _⊑₁_)
    module CP₂ = ConPreorder CP₂ renaming (_⊑_ to _⊑₂_)

    module M  = SatMor m
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂

    module H = Hetero.For m P₁ P₂

    module MF = MuFusion.For CP₁ CP₂

    -- Pull back target satisfaction along `mapCtx` (for readability).
    SatF₂↑ : Ctx₁ → P2.Form → Set ℓSat₂
    SatF₂↑ = H.SatF₂↑

    -- Convenience: satisfaction on exported constraints.
    SatF₂-Export : ∀ p c → SatF₂↑ p (P2.Export c) ↔ Sat₂ (M.mapCtx p) c
    SatF₂-Export p c = Prop.↔-sym (P2.SatC≈F (M.mapCtx p) c)

  -- -------------------------------------------------------------------------
  -- Canonical agreement on exports (constraints).
  --
  -- Translating an exported constraint is observationally the same as exporting
  -- the mapped constraint.
  -- -------------------------------------------------------------------------

  translate-export
    : ∀ p (c : Con₁)
    → SatF₂↑ p (H.translate (P1.Export c))
        ↔
      SatF₂↑ p (P2.Export (M.mapCon c))
  translate-export p c =
    let
      -- Reduce `translate` using its semantic preservation, then expose the SatMor.
      step₁ : SatF₂↑ p (H.translate (P1.Export c)) ↔ P1.SatF p (P1.Export c)
      step₁ = Prop.↔-sym (H.translate-preserves-Sat p (P1.Export c))

      step₂ : P1.SatF p (P1.Export c) ↔ Sat₁ p c
      step₂ = Prop.↔-sym (P1.SatC≈F p c)

      step₃ : Sat₁ p c ↔ Sat₂ (M.mapCtx p) (M.mapCon c)
      step₃ = M.sat-↔ p c

      step₄ : Sat₂ (M.mapCtx p) (M.mapCon c) ↔ SatF₂↑ p (P2.Export (M.mapCon c))
      step₄ = Prop.↔-sym (SatF₂-Export p (M.mapCon c))
    in
    Prop.↔-trans step₁ (Prop.↔-trans step₂ (Prop.↔-trans step₃ step₄))

  -- -------------------------------------------------------------------------
  -- μ-level transport for exported fixed points (Kleene μ on constraints).
  --
  -- This is the “limit-level” analogue of ported closure naturality:
  -- the statement is phrased as an observational preorder on the target
  -- satisfaction (soundness direction), with explicit ωCPO/continuity hypotheses.
  -- -------------------------------------------------------------------------

  record MuTransportData
    (ω₁ : Truth.GuardedCore.OmegaCPO CP₁)
    (ω₂ : Truth.GuardedCore.OmegaCPO CP₂)
    (F₁ : Con₁ → Con₁)
    (F₂ : Con₂ → Con₂)
    : Set (lsuc (ℓCtx₁ ⊔ ℓCtx₂ ⊔ ℓCon₁ ⊔ ℓCon₂ ⊔ ℓSat₁ ⊔ ℓSat₂)) where
    field
      -- Map structure: monotone + strict⊥ + ω-continuous (for chains).
      Mω : MF.OmegaCPOMap ω₁ ω₂ M.mapCon

      -- Step/operator assumptions.
      monoF₂ : MonoOn CP₂ F₂
      inflF₁ : ∀ c → CP₁._⊑₁_ c (F₁ c)
      comm   : ∀ c → CP₂._⊑₂_ (M.mapCon (F₁ c)) (F₂ (M.mapCon c))

      -- Satisfaction monotonicity w.r.t. the constraint preorder on the target.
      monoSat₂ : ∀ {p : Ctx₂} {c d : Con₂}
               → CP₂._⊑₂_ c d → Sat₂ p c → Sat₂ p d

  -- Variant with a weaker (and more literal) satisfaction monotonicity hypothesis:
  -- we only ever use monotonicity at contexts of the form `mapCtx p` (pulled back
  -- along the SatMor). This keeps assumptions explicit while avoiding an
  -- unnecessarily global monotonicity requirement on all target contexts.
  record MuTransportData↑
    (ω₁ : Truth.GuardedCore.OmegaCPO CP₁)
    (ω₂ : Truth.GuardedCore.OmegaCPO CP₂)
    (F₁ : Con₁ → Con₁)
    (F₂ : Con₂ → Con₂)
    : Set (lsuc (ℓCtx₁ ⊔ ℓCtx₂ ⊔ ℓCon₁ ⊔ ℓCon₂ ⊔ ℓSat₁ ⊔ ℓSat₂)) where
    field
      -- Map structure: monotone + strict⊥ + ω-continuous (for chains).
      Mω : MF.OmegaCPOMap ω₁ ω₂ M.mapCon

      -- Step/operator assumptions.
      monoF₂ : MonoOn CP₂ F₂
      inflF₁ : ∀ c → CP₁._⊑₁_ c (F₁ c)
      comm   : ∀ c → CP₂._⊑₂_ (M.mapCon (F₁ c)) (F₂ (M.mapCon c))

      -- Monotonicity only along the image of `mapCtx`.
      monoSat₂↑ : ∀ {p : Ctx₁} {c d : Con₂}
                → CP₂._⊑₂_ c d → Sat₂ (M.mapCtx p) c → Sat₂ (M.mapCtx p) d

  -- Transport with the weakened monotonicity hypothesis.
  translate-μ≤↑
    : ∀ {ω₁ : Truth.GuardedCore.OmegaCPO CP₁}
        {ω₂ : Truth.GuardedCore.OmegaCPO CP₂}
        {F₁ : Con₁ → Con₁}
        {F₂ : Con₂ → Con₂}
    → MuTransportData↑ ω₁ ω₂ F₁ F₂
    → ∀ p
    → SatF₂↑ p (H.translate (P1.Export (Truth.GuardedCore.Kleene.μ ω₁ F₁)))
    → SatF₂↑ p (P2.Export (Truth.GuardedCore.Kleene.μ ω₂ F₂))
  translate-μ≤↑ {ω₁ = ω₁} {ω₂ = ω₂} {F₁ = F₁} {F₂ = F₂} A p sat =
    let
      open MuTransportData↑ A

      μ₁ = Truth.GuardedCore.Kleene.μ ω₁ F₁
      μ₂ = Truth.GuardedCore.Kleene.μ ω₂ F₂

      -- μ-fusion on constraints.
      mapμ≤μ : CP₂._⊑₂_ (M.mapCon μ₁) μ₂
      mapμ≤μ =
        MF.μ-fusion≤ Mω F₁ F₂ monoF₂ inflF₁ comm

      -- Move the premise to Sat₂ on `mapCon μ₁`.
      prem₀ : SatF₂↑ p (P2.Export (M.mapCon μ₁))
      prem₀ = Prop.to (translate-export p μ₁) sat

      prem₁ : Sat₂ (M.mapCtx p) (M.mapCon μ₁)
      prem₁ = Prop.to (SatF₂-Export p (M.mapCon μ₁)) prem₀

      concl₀ : Sat₂ (M.mapCtx p) μ₂
      concl₀ = monoSat₂↑ mapμ≤μ prem₁

      concl₁ : SatF₂↑ p (P2.Export μ₂)
      concl₁ = Prop.from (SatF₂-Export p μ₂) concl₀
    in
    concl₁

  -- Transport: translated export of `μ F₁` semantically implies export of `μ F₂`.
  translate-μ≤
    : ∀ {ω₁ : Truth.GuardedCore.OmegaCPO CP₁}
        {ω₂ : Truth.GuardedCore.OmegaCPO CP₂}
        {F₁ : Con₁ → Con₁}
        {F₂ : Con₂ → Con₂}
    → MuTransportData ω₁ ω₂ F₁ F₂
    → ∀ p
    → SatF₂↑ p (H.translate (P1.Export (Truth.GuardedCore.Kleene.μ ω₁ F₁)))
    → SatF₂↑ p (P2.Export (Truth.GuardedCore.Kleene.μ ω₂ F₂))
  translate-μ≤ A p sat =
    let
      open MuTransportData A

      A↑ : MuTransportData↑ _ _ _ _
      A↑ =
        record
          { Mω = Mω
          ; monoF₂ = monoF₂
          ; inflF₁ = inflF₁
          ; comm = comm
          ; monoSat₂↑ = λ {p} le → monoSat₂ le
          }
    in
    translate-μ≤↑ A↑ p sat
