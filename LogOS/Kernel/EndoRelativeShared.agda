{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.EndoRelativeShared where

open import LogOS.Prelude

open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Minimal.Closure using (ClosureOp; cl; infl; idemp-lax) renaming (mono to mono-cl)

import LogOS.Kernel.EndoCoreShared as CoreShared

module With
  {ℓObj ℓ : Level}
  (Obj : Set ℓObj)
  (BBOf : Obj → BulkBoundary ℓ)
  where

  module Core = CoreShared.With Obj BBOf
  open Core public
    using
      ( Endo; _≤₂_; _≈₂_; idEndo; _∘E_
      ; refl₂; trans₂
      )

  open Endo public

  module For
    (K : Obj)
    (C : ClosureOp (BulkBoundary.bnd (BBOf K)))
    where

    private
      CP : ConPreorder ℓ
      CP = BulkBoundary.bnd (BBOf K)

    J : Endo K
    J =
      record
        { fn   = cl C
        ; mono = mono-cl C
        }

    id≤J : _≤₂_ K (idEndo K) J
    id≤J = infl C

    J∘J≤J : _≤₂_ K (J ∘E J) J
    J∘J≤J = idemp-lax C

    J-closeEndo : Endo K → Endo K
    J-closeEndo f = J ∘E f

    J-close-mono
      : ∀ {f g}
      → _≤₂_ K f g
      → _≤₂_ K (J-closeEndo f) (J-closeEndo g)
    J-close-mono le = λ c → Endo.mono J (le c)

    J-close-respects≈₂
      : ∀ {f g}
      → _≈₂_ K f g
      → _≈₂_ K (J-closeEndo f) (J-closeEndo g)
    J-close-respects≈₂ {f} {g} (fg , gf) =
      ( J-close-mono {f = f} {g = g} fg
      , J-close-mono {f = g} {g = f} gf
      )

    id≤J-close
      : ∀ (f : Endo K)
      → _≤₂_ K (idEndo K) f
      → _≤₂_ K (idEndo K) (J-closeEndo f)
    id≤J-close f id≤f = λ c →
      ConPreorder.trans CP (id≤f c) (id≤J (Endo.fn f c))

    J-close≤J
      : ∀ (f : Endo K)
      → _≤₂_ K f J
      → _≤₂_ K (J-closeEndo f) J
    J-close≤J f f≤J = λ c →
      let
        step₁ = Endo.mono J (f≤J c)
        step₂ = J∘J≤J c
      in ConPreorder.trans CP step₁ step₂

    J≤J-close
      : ∀ (f : Endo K)
      → _≤₂_ K (idEndo K) f
      → _≤₂_ K J (J-closeEndo f)
    J≤J-close f id≤f = λ c → Endo.mono J (id≤f c)

    record ClosureStep : Set (lsuc ℓ) where
      field
        endo  : Endo K
        infl  : _≤₂_ K (idEndo K) endo
        leJ   : _≤₂_ K endo J

    open ClosureStep public

    mkClosureStep
      : (f : Endo K)
      → _≤₂_ K (idEndo K) f
      → _≤₂_ K f J
      → ClosureStep
    mkClosureStep f infl leJ = record { endo = f ; infl = infl ; leJ = leJ }

    J-closeStep : ClosureStep → ClosureStep
    J-closeStep s =
      mkClosureStep
        (J-closeEndo (endo s))
        (id≤J-close (endo s) (infl s))
        (J-close≤J (endo s) (leJ s))

    _∘Step_ : ClosureStep → ClosureStep → ClosureStep
    _∘Step_ s₂ s₁ =
      let
        f = endo s₁
        g = endo s₂
        inflf = infl s₁
        inflg = infl s₂
        f≤J  = leJ s₁
        g≤J  = leJ s₂
        g-mono = Endo.mono g
      in
      mkClosureStep
        (g ∘E f)
        (λ c -> ConPreorder.trans CP (inflg c) (g-mono (inflf c)))
        (λ c ->
          ConPreorder.trans CP
            (ConPreorder.trans CP
              (g-mono (f≤J c))
              (g≤J (Endo.fn J c)))
            (J∘J≤J c))

    infixr 9 _∘Step_

    _thenStep_ : ClosureStep → ClosureStep → ClosureStep
    _thenStep_ s₁ s₂ = s₂ ∘Step s₁

    infixl 9 _thenStep_

  module FromClosureOp
    (K : Obj)
    (C : ClosureOp (BulkBoundary.bnd (BBOf K)))
    where

    module Rel = For K C
    open Rel public
