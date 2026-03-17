{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Opacity.TagOpacity where

-- Opacity as factorisation:
-- a discrete private view on code factors through a coarser public observation
-- that forgets the hidden tag.
-- This is intentionally a single-view slice of the shared observation
-- discipline, not a standalone app-local architecture.

open import LogOS.Prelude
open import LogOS.Prelude.Fin using (fzero; fsuc; _≢_)
open import LogOS.LT.ConPreorder using (ConPreorder; refl⊑)
open import LogOS.LT.ConPreorder.Discrete using (DiscretePreorder)
open import LogOS.LT.Kernel using (Code; bnd; decode)
open import LogOS.LT.Contracts using
  ( ContractHom
  ; KernelOf
  ; ConOf
  ; _⊨_[_]
  ; models-map-contract
  ; hom
  )
open import LogOS.LT.Hom.Core using (mapCode)
open import LogOS.LT.View using (View; idView)
open import LogOS.LT.View.Factorisation using (FactorisesThrough)
open import LogOS.Ports.Opacity.Port using (OpacityPort)
import LogOS.Ports.Opacity.Port as Opacity
open import LogOS.Ports.Opacity.Factorisation using
  ( OpacityFactorisation
  ; privateContract
  ; publicContract
  ; factorisationContractHom
  )
open import LogOS.Ports.Opacity.Distinguishability using
  ( DistinguishableFamily
  ; family
  )
open import LogOS.Ports.Opacity.Obstruction using
  ( OpaqueFamily
  ; source
  ; PublicReadbackOn
  ; opaqueFamily-obstructsPublicReadbackOn
  )

import LogOS.Apps.Opacity.Demo as Demo

PrivatePreorder : ConPreorder _ _
PrivatePreorder = DiscretePreorder (Code Demo.K)

privateView : View (Code Demo.K) PrivatePreorder
privateView = idView PrivatePreorder

publicView : View (Code Demo.K) (bnd Demo.K)
publicView = Opacity.toView Demo.codeOpacity

privatePort : OpacityPort (Code Demo.K) PrivatePreorder
privatePort = Opacity.fromView privateView

publicPort : OpacityPort (Code Demo.K) (bnd Demo.K)
publicPort = Demo.codeOpacity

private
  tag₀ : Code Demo.K
  tag₀ = (zero , zero)

  tag₁ : Code Demo.K
  tag₁ = (zero , suc zero)

  tag₀≢tag₁ : tag₀ ≢ tag₁
  tag₀≢tag₁ ()

tagFactorisation : FactorisesThrough privateView publicView
tagFactorisation =
  record
    { collapse = decode Demo.K
    ; collapse-mono = λ { refl → refl⊑ (bnd Demo.K) }
    ; commute = λ _ → (refl⊑ (bnd Demo.K) , refl⊑ (bnd Demo.K))
    }

tagOpacityFactorisation : OpacityFactorisation privatePort publicPort
tagOpacityFactorisation = record { factorisation = tagFactorisation }

exactTag₀Contract = privateContract tagOpacityFactorisation tag₀

publicZeroContract = publicContract tagOpacityFactorisation zero

exactTag₀⇒publicZero : ContractHom exactTag₀Contract publicZeroContract
exactTag₀⇒publicZero =
  factorisationContractHom tagOpacityFactorisation (refl⊑ (bnd Demo.K))

tag₀-satisfies-exact : KernelOf exactTag₀Contract ⊨ tag₀ [ ConOf exactTag₀Contract ]
tag₀-satisfies-exact = refl⊑ PrivatePreorder

tag₀-satisfies-public : KernelOf publicZeroContract ⊨ mapCode (hom exactTag₀⇒publicZero) tag₀ [ ConOf publicZeroContract ]
tag₀-satisfies-public = models-map-contract exactTag₀⇒publicZero tag₀-satisfies-exact

sourceFamily : DistinguishableFamily privateView
sourceFamily =
  record
    { family =
        record
          { size = suc (suc zero)
          ; at = λ where
              fzero → tag₀
              (fsuc fzero) → tag₁
          }
    ; separated = λ where
        fzero fzero neq _ → neq refl
        fzero (fsuc fzero) neq eq → tag₀≢tag₁ (fst eq)
        (fsuc fzero) fzero neq eq → tag₀≢tag₁ (snd eq)
        (fsuc fzero) (fsuc fzero) neq _ → neq refl
    }

tagOpacityOpaqueFamily : OpaqueFamily tagFactorisation
tagOpacityOpaqueFamily =
  record
    { source = sourceFamily
    ; i = fzero
    ; k = fsuc fzero
    ; distinct = λ ()
    ; publicCollapsed =
        Demo.tag-opaque⊑ zero zero (suc zero)
      , Demo.tag-opaque⊑ zero (suc zero) zero
    }

publicObservation-noReadbackOnTags
  : ¬ PublicReadbackOn (family (source tagOpacityOpaqueFamily)) privateView publicView
publicObservation-noReadbackOnTags =
  opaqueFamily-obstructsPublicReadbackOn tagOpacityOpaqueFamily
