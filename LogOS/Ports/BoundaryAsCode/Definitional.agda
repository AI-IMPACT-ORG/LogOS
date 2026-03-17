{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.BoundaryAsCode.Definitional where

-- Definitional/bookkeeping equalities for strict boundary-as-code denotations.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Kernel using (decode)
open import LogOS.Ports.BoundaryAsCode using (boundaryKernel)
open import LogOS.Ports.Locality.Core using (LocalityPort; LocalBoundary; localKernel)
open import LogOS.Ports.BoundaryTransparency.Definitional using
  ( BoundaryTransparent≡
  ; decode-mapCode-transparent≡
  ; transportCon≡
  ; untransportCon≡
  ; untransportCon-transportCon≡
  )
import LogOS.LT.Hom.Strictification as StrictHom

transparent-mapCode≡decode
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → (yo : StrictHom.KernelHom≡ (localKernel P) (boundaryKernel I O))
  → (bt : BoundaryTransparent≡ yo)
  → ∀ x
  → StrictHom.mapCode yo x ≡ transportCon≡ bt (decode (localKernel P) x)
transparent-mapCode≡decode _ yo bt x =
  decode-mapCode-transparent≡ bt x

transparent-mapCode-normalised
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → (yo : StrictHom.KernelHom≡ (localKernel P) (boundaryKernel I O))
  → (bt : BoundaryTransparent≡ yo)
  → ∀ x
  → untransportCon≡ bt (StrictHom.mapCode yo x)
    ≡
    decode (localKernel P) x
transparent-mapCode-normalised P yo bt x
  rewrite transparent-mapCode≡decode P yo bt x
        | untransportCon-transportCon≡ bt (decode (localKernel P) x)
  = refl

transparent-mapCode-unique
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    {X : Set ℓX}
  → (P : LocalityPort X I O)
  → (yo₁ yo₂ : StrictHom.KernelHom≡ (localKernel P) (boundaryKernel I O))
  → (bt₁ : BoundaryTransparent≡ yo₁)
  → (bt₂ : BoundaryTransparent≡ yo₂)
  → ∀ x
  → untransportCon≡ bt₁ (StrictHom.mapCode yo₁ x)
    ≡
    untransportCon≡ bt₂ (StrictHom.mapCode yo₂ x)
transparent-mapCode-unique P yo₁ yo₂ bt₁ bt₂ x =
  trans
    (transparent-mapCode-normalised P yo₁ bt₁ x)
    (sym (transparent-mapCode-normalised P yo₂ bt₂ x))
