{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.MuFusion where

-- μ-fusion / naturality for Kleene μ (least pre-fixed points).
--
-- Core idea:
-- if a map between ωCPO preorders preserves ⊥ and ω-sups (for chains) and commutes
-- laxly with an operator, then it transports the Kleene μ construction as an
-- inequality `map (μ F) ⊑ μ G`.
--
-- This is the “one lemma to thread them all” for transporting μ-style stability
-- statements across adapters once the relevant order/continuity assumptions are
-- provided.

open import LogOS.Prelude
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
import LogOS.Minimal.MuFusion as MuFusionCore
import LogOS.Theorems.Boundary.ContinuityCore as ContinuityCore

module For
  {ℓ₁ ℓ₂ : Level}
  (CP₁ : ConPreorder ℓ₁)
  (CP₂ : ConPreorder ℓ₂)
  where

  -- Minimal-layer core (ωCPO maps + μ-fusion).
  --
  -- This keeps Ports/Computation free of Theorems imports while ensuring a
  -- single source of truth for the underlying structure/lemma.
  open MuFusionCore.For CP₁ CP₂ public

  -- -------------------------------------------------------------------------
  -- Corollary: transport the distinguished stabilised truth `Th*`.
  --
  -- If both guarded closures are equipped with FiniteFirst+OmegaCPO data, then
  -- `Th*` is (up to the preorder) the Kleene `μ` of `Flow`. Combined with
  -- `μ-fusion≤`, this yields derived preservation of `Th*` from preservation of
  -- `Flow` plus ωCPO-map structure for `map`.
  -- -------------------------------------------------------------------------

  preserves-Th*-from-Flow
    : ∀ {ω₁ : GC₁.OmegaCPO CP₁} {ω₂ : GC₂.OmegaCPO CP₂}
      {map : Con₁ → Con₂}
      (M : OmegaCPOMap ω₁ ω₂ map)
      (G₁ : GC₁.GuardedClosure CP₁)
      (G₂ : GC₂.GuardedClosure CP₂)
      (FF₁ : GC₁.FiniteFirst CP₁ G₁ ω₁)
      (FF₂ : GC₂.FiniteFirst CP₂ G₂ ω₂)
      (comm : ∀ c → _⊑₂_ (map (GC₁.GuardedClosure.Flow G₁ c))
                         (GC₂.GuardedClosure.Flow G₂ (map c)))
    → _⊑₂_ (map (GC₁.GuardedClosure.Th* G₁)) (GC₂.GuardedClosure.Th* G₂)
  preserves-Th*-from-Flow {ω₁ = ω₁} {ω₂ = ω₂} {map = map} M G₁ G₂ FF₁ FF₂ comm =
    trans₂
      (mono-map th₁≤μ₁)
      (trans₂
        (μ-fusion≤ M F₁ F₂ monoF₂ inflF₁ comm)
        μ₂≤th₂)
    where
      open OmegaCPOMap M
      open GC₁.GuardedClosure G₁ renaming (Flow to F₁; Th* to Th₁; infl to inflF₁)
      open GC₂.GuardedClosure G₂ renaming (Flow to F₂; Th* to Th₂; mono to monoF₂)

      module C₁ = ContinuityCore.For CP₁ G₁
      module C₂ = ContinuityCore.For CP₂ G₂

      th₁≤μ₁ : _⊑₁_ Th₁ (GC₁.Kleene.μ ω₁ F₁)
      th₁≤μ₁ = C₁.Th*≤μFlow ω₁ FF₁

      μ₂≤th₂ : _⊑₂_ (GC₂.Kleene.μ ω₂ F₂) Th₂
      μ₂≤th₂ = C₂.μFlow≤Th* ω₂ FF₂

  -- Bundle the hypotheses for `preserves-Th*-from-Flow` so call sites can name
  -- the assumptions explicitly.

  record Th*TransportAssumptions
    (ω₁ : GC₁.OmegaCPO CP₁)
    (ω₂ : GC₂.OmegaCPO CP₂)
    (map : Con₁ → Con₂)
    (G₁ : GC₁.GuardedClosure CP₁)
    (G₂ : GC₂.GuardedClosure CP₂)
    : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    open GC₁.GuardedClosure G₁ renaming (Flow to F₁)
    open GC₂.GuardedClosure G₂ renaming (Flow to F₂)
    field
      M    : OmegaCPOMap ω₁ ω₂ map
      FF₁  : GC₁.FiniteFirst CP₁ G₁ ω₁
      FF₂  : GC₂.FiniteFirst CP₂ G₂ ω₂
      comm : ∀ c → _⊑₂_ (map (F₁ c)) (F₂ (map c))

  preserves-Th*-from-Flowᵃ
    : ∀ {ω₁ : GC₁.OmegaCPO CP₁} {ω₂ : GC₂.OmegaCPO CP₂}
      {map : Con₁ → Con₂}
      (G₁ : GC₁.GuardedClosure CP₁)
      (G₂ : GC₂.GuardedClosure CP₂)
    → Th*TransportAssumptions ω₁ ω₂ map G₁ G₂
    → _⊑₂_ (map (GC₁.GuardedClosure.Th* G₁)) (GC₂.GuardedClosure.Th* G₂)
  preserves-Th*-from-Flowᵃ {map = map} G₁ G₂ A =
    preserves-Th*-from-Flow (Th*TransportAssumptions.M A) G₁ G₂
      (Th*TransportAssumptions.FF₁ A)
      (Th*TransportAssumptions.FF₂ A)
      (Th*TransportAssumptions.comm A)

-- -------------------------------------------------------------------------
-- OmegaCPOMap infrastructure (identity/composition).
-- -------------------------------------------------------------------------

module Endo {ℓ : Level} (CP : ConPreorder ℓ) where
  module F = For CP CP
  open F

  idOmegaCPOMap
    : ∀ {ω : GC₁.OmegaCPO CP}
    → OmegaCPOMap ω ω (λ x → x)
  idOmegaCPOMap {ω = ω} =
    record
      { mono-map = idMonoMap {CP = CP}
      ; strict⊥  = ConPreorder.refl CP
      ; cont-ω   = λ _ _ → ConPreorder.refl CP
      }

  module Experimental where
    open ConPreorder CP renaming (Con to Con; _⊑_ to _⊑_; trans to trans⊑)

    record FlowSymmetryAssumptions
      (ω : GC₁.OmegaCPO CP)
      (G : GC₁.GuardedClosure CP)
      (map back : Con → Con)
      : Set (lsuc ℓ) where
      field
        mapA  : Th*TransportAssumptions ω ω map G G
        backA : Th*TransportAssumptions ω ω back G G

        section-map-back : ∀ c → c ⊑ map (back c)
        section-back-map : ∀ c → c ⊑ back (map c)

    Th*-≈-map
      : ∀ {ω : GC₁.OmegaCPO CP}
        {G : GC₁.GuardedClosure CP}
        {map back : Con → Con}
      → FlowSymmetryAssumptions ω G map back
      → _≈CP_ CP (map (GC₁.GuardedClosure.Th* G)) (GC₁.GuardedClosure.Th* G)
    Th*-≈-map {G = G} {map = map} {back = back} A =
      mapTh*≤Th* , Th*≤mapTh*
      where
        open FlowSymmetryAssumptions A

        mapTh*≤Th* : map (GC₁.GuardedClosure.Th* G) ⊑ GC₁.GuardedClosure.Th* G
        mapTh*≤Th* = preserves-Th*-from-Flowᵃ G G mapA

        backTh*≤Th* : back (GC₁.GuardedClosure.Th* G) ⊑ GC₁.GuardedClosure.Th* G
        backTh*≤Th* = preserves-Th*-from-Flowᵃ G G backA

        Th*≤mapTh* : GC₁.GuardedClosure.Th* G ⊑ map (GC₁.GuardedClosure.Th* G)
        Th*≤mapTh* =
          trans⊑
            (section-map-back (GC₁.GuardedClosure.Th* G))
            (OmegaCPOMap.mono-map (Th*TransportAssumptions.M mapA) backTh*≤Th*)

    Th*-≈-back
      : ∀ {ω : GC₁.OmegaCPO CP}
        {G : GC₁.GuardedClosure CP}
        {map back : Con → Con}
      → FlowSymmetryAssumptions ω G map back
      → _≈CP_ CP (back (GC₁.GuardedClosure.Th* G)) (GC₁.GuardedClosure.Th* G)
    Th*-≈-back {G = G} {map = map} {back = back} A =
      backTh*≤Th* , Th*≤backTh*
      where
        open FlowSymmetryAssumptions A

        mapTh*≤Th* : map (GC₁.GuardedClosure.Th* G) ⊑ GC₁.GuardedClosure.Th* G
        mapTh*≤Th* = preserves-Th*-from-Flowᵃ G G mapA

        backTh*≤Th* : back (GC₁.GuardedClosure.Th* G) ⊑ GC₁.GuardedClosure.Th* G
        backTh*≤Th* = preserves-Th*-from-Flowᵃ G G backA

        Th*≤backTh* : GC₁.GuardedClosure.Th* G ⊑ back (GC₁.GuardedClosure.Th* G)
        Th*≤backTh* =
          trans⊑
            (section-back-map (GC₁.GuardedClosure.Th* G))
            (OmegaCPOMap.mono-map (Th*TransportAssumptions.M backA) mapTh*≤Th*)

module Compose
  {ℓ₁ ℓ₂ ℓ₃ : Level}
  (CP₁ : ConPreorder ℓ₁)
  (CP₂ : ConPreorder ℓ₂)
  (CP₃ : ConPreorder ℓ₃)
  where

  module F₁₂ = For CP₁ CP₂
  module F₂₃ = For CP₂ CP₃
  module F₁₃ = For CP₁ CP₃

  open ConPreorder CP₁ renaming (Con to Con₁; _⊑_ to _⊑₁_)
  open ConPreorder CP₂ renaming (Con to Con₂; _⊑_ to _⊑₂_)
  open ConPreorder CP₃ renaming (Con to Con₃; trans to trans₃)

  composeOmegaCPOMap
    : ∀ {ω₁ : F₁₂.GC₁.OmegaCPO CP₁}
        {ω₂ : F₁₂.GC₂.OmegaCPO CP₂}
        {ω₃ : F₂₃.GC₂.OmegaCPO CP₃}
        {map₁₂ : Con₁ → Con₂}
        {map₂₃ : Con₂ → Con₃}
      (M₁₂ : F₁₂.OmegaCPOMap ω₁ ω₂ map₁₂)
      (M₂₃ : F₂₃.OmegaCPOMap ω₂ ω₃ map₂₃)
    → F₁₃.OmegaCPOMap ω₁ ω₃ (λ x → map₂₃ (map₁₂ x))
  composeOmegaCPOMap {ω₁ = ω₁} {ω₂ = ω₂} {ω₃ = ω₃} {map₁₂ = map₁₂} {map₂₃ = map₂₃} M₁₂ M₂₃ =
    record
      { mono-map =
          compMonoMap {CP₁ = CP₁} {CP₂ = CP₂} {CP₃ = CP₃} {f = map₁₂} {g = map₂₃}
            (F₁₂.OmegaCPOMap.mono-map M₁₂)
            (F₂₃.OmegaCPOMap.mono-map M₂₃)
      ; strict⊥ =
          trans₃
            (F₂₃.OmegaCPOMap.mono-map M₂₃ (F₁₂.OmegaCPOMap.strict⊥ M₁₂))
            (F₂₃.OmegaCPOMap.strict⊥ M₂₃)
      ; cont-ω = λ f mono-chain →
          let
            module M₁₂ = F₁₂.OmegaCPOMap M₁₂
            module M₂₃ = F₂₃.OmegaCPOMap M₂₃

            chain₂ : ∀ n → _⊑₂_ (map₁₂ (f n)) (map₁₂ (f (suc n)))
            chain₂ n = M₁₂.mono-map (mono-chain n)
          in
          trans₃
            (M₂₃.mono-map (M₁₂.cont-ω f mono-chain))
            (M₂₃.cont-ω (λ n → map₁₂ (f n)) chain₂)
      }

-- -------------------------------------------------------------------------
-- Kernel-specialised “upgrade” constructors.
-- -------------------------------------------------------------------------

module Kernel where
  open import LogOS.Base.Signature
  open import LogOS.Minimal.Adapter
  open import LogOS.Minimal.ConAlg
  open import LogOS.Kernel
  open import LogOS.Kernel.Hom

  module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
    private
      module GT = Truth.GuardedCore {ℓ = ℓ}

    module _ {K₁ K₂ : Kernel Sig Q} {h : KernelHom K₁ K₂} where
      private
        CP₁ : ConPreorder ℓ
        CP₁ = BulkBoundary.bnd (Kernel.BB K₁)

        CP₂ : ConPreorder ℓ
        CP₂ = BulkBoundary.bnd (Kernel.BB K₂)

        map∂ : ConPreorder.Con CP₁ → ConPreorder.Con CP₂
        map∂ = ConAlgHom≡.map∂ (KernelHom.con-hom h)

        module MF = For CP₁ CP₂

      -- Bundle the domain-theoretic assumptions used to derive `KernelHomFlowStable`
      -- from `KernelHomFlow` via μ-fusion.

      record KernelHomStabilisationAssumptions : Set (lsuc (lsuc ℓ)) where
        field
          ω₁ : GT.OmegaCPO CP₁
          ω₂ : GT.OmegaCPO CP₂

          M : MF.OmegaCPOMap ω₁ ω₂ map∂

          FF₁ : GT.FiniteFirst CP₁ (GTruth K₁) ω₁
          FF₂ : GT.FiniteFirst CP₂ (GTruth K₂) ω₂

      kernelHomFlowStable-from
        : (hf : KernelHomFlow K₁ K₂ h)
        → KernelHomStabilisationAssumptions
        → KernelHomFlowStable K₁ K₂ h
      kernelHomFlowStable-from hf A =
        let
          open KernelHomFlow hf
          module FH = GT.FlowHom flow-hom

          comm : ∀ c →
            ConPreorder._⊑_ CP₂
              (map∂ (GT.GuardedClosure.Flow (GTruth K₁) c))
              (GT.GuardedClosure.Flow (GTruth K₂) (map∂ c))
          comm = FH.preserves-F

          preservesTh : ConPreorder._⊑_ CP₂
                          (map∂ (GT.GuardedClosure.Th* (GTruth K₁)))
                          (GT.GuardedClosure.Th* (GTruth K₂))
          preservesTh =
            MF.preserves-Th*-from-Flow
              (KernelHomStabilisationAssumptions.M A)
              (GTruth K₁)
              (GTruth K₂)
              (KernelHomStabilisationAssumptions.FF₁ A)
              (KernelHomStabilisationAssumptions.FF₂ A)
              comm
        in
        record
          { stable-hom =
              record
                { flow-hom     = flow-hom
                ; preserves-Th = preservesTh
                }
          }

module GradedKernel where
  open import LogOS.Base.Signature
  open import LogOS.Minimal.Adapter
  open import LogOS.Minimal.ConAlg
  open import LogOS.Kernel.Graded
  open import LogOS.Kernel.Graded.Hom

  module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
    private
      module GT = Truth.GuardedCore {ℓ = ℓ}

    module _ {K₁ K₂ : GradedKernel Sig Q} {h : GradedKernelHom K₁ K₂} where
      private
        CP₁ : ConPreorder ℓ
        CP₁ = BulkBoundary.bnd (GradedKernel.BB K₁)

        CP₂ : ConPreorder ℓ
        CP₂ = BulkBoundary.bnd (GradedKernel.BB K₂)

        map∂ : ConPreorder.Con CP₁ → ConPreorder.Con CP₂
        map∂ = ConAlgHom≡.map∂ (GradedKernelHom.con-hom h)

        module MF = For CP₁ CP₂

        GC₁sat : GT.GuardedClosure CP₁
        GC₁sat = GT.forgetGradedClosure (GradedKernel.GTruth K₁)

        GC₂sat : GT.GuardedClosure CP₂
        GC₂sat = GT.forgetGradedClosure (GradedKernel.GTruth K₂)

      -- Bundle the domain-theoretic assumptions used to derive
      -- `GradedKernelHomFlowStable` from `GradedKernelHomFlow` at the saturation
      -- grade via μ-fusion.

      record GradedKernelHomStabilisationAssumptions : Set (lsuc (lsuc ℓ)) where
        field
          ω₁ : GT.OmegaCPO CP₁
          ω₂ : GT.OmegaCPO CP₂

          M : MF.OmegaCPOMap ω₁ ω₂ map∂

          FF₁ : GT.FiniteFirst CP₁ GC₁sat ω₁
          FF₂ : GT.FiniteFirst CP₂ GC₂sat ω₂

      gradedKernelHomFlowStable-from
        : (hf : GradedKernelHomFlow K₁ K₂ h)
        → GradedKernelHomStabilisationAssumptions
        → GradedKernelHomFlowStable K₁ K₂ h
      gradedKernelHomFlowStable-from hf A =
        let
          open GradedKernelHomFlow hf

          flowSat : GT.FlowHom CP₁ CP₂ GC₁sat GC₂sat map∂
          flowSat = GT.forgetGradedFlowHom flow-hom
          module FHSat = GT.FlowHom flowSat

          comm : ∀ c →
            ConPreorder._⊑_ CP₂
              (map∂ (GT.GuardedClosure.Flow GC₁sat c))
              (GT.GuardedClosure.Flow GC₂sat (map∂ c))
          comm = FHSat.preserves-F

          preservesTh : ConPreorder._⊑_ CP₂
                          (map∂ (GradedClosure.Th* (GradedKernel.GTruth K₁)))
                          (GradedClosure.Th* (GradedKernel.GTruth K₂))
          preservesTh =
            MF.preserves-Th*-from-Flow
              (GradedKernelHomStabilisationAssumptions.M A)
              GC₁sat
              GC₂sat
              (GradedKernelHomStabilisationAssumptions.FF₁ A)
              (GradedKernelHomStabilisationAssumptions.FF₂ A)
              comm
        in
        record
          { stable-hom =
              record
                { flow-hom     = flow-hom
                ; preserves-Th = preservesTh
                }
          ; step≤ = step≤
          }
