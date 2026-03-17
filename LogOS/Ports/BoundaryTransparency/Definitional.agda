{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.BoundaryTransparency.Definitional where

-- Definitional/bookkeeping equalities for boundary transparency.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; ≡→≈)
open import LogOS.LT.Kernel using (Kernel; bnd; decode)
open import LogOS.Ports.BoundaryTransparency using (BoundaryTransparent)
import LogOS.LT.Hom.Strictification as StrictHom

record BoundaryTransparent≡
  {ℓ ℓRel ℓCode ℓCode' : Level}
  {K : Kernel ℓ ℓRel ℓCode}
  {K' : Kernel ℓ ℓRel ℓCode'}
  (h : StrictHom.KernelHom≡ K K') : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode ⊔ ℓCode')) where
  field
    bnd≡≡ : bnd K ≡ bnd K'
    map∂-transparent≡ : ∀ c → StrictHom.map∂ h c ≡ subst Con bnd≡≡ c

  decode-mapCode-transparent≡
    : ∀ γ → decode K' (StrictHom.mapCode h γ) ≡ subst Con bnd≡≡ (decode K γ)
  decode-mapCode-transparent≡ γ =
    trans
      (StrictHom.decode-mapCode≡ h γ)
      (map∂-transparent≡ (decode K γ))

open BoundaryTransparent≡ public

strict→approxBoundaryTransparent
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : StrictHom.KernelHom≡ K K'}
  → BoundaryTransparent≡ h
  → BoundaryTransparent (StrictHom.strict→approx h)
strict→approxBoundaryTransparent {K' = K'} bt =
  record
    { bnd≡ = BoundaryTransparent≡.bnd≡≡ bt
    ; map∂-transparent≈ =
        λ c → ≡→≈ {CP = bnd K'} (BoundaryTransparent≡.map∂-transparent≡ bt c)
    }

transportCon≡
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : StrictHom.KernelHom≡ K K'}
  → BoundaryTransparent≡ h
  → Con (bnd K)
  → Con (bnd K')
transportCon≡ bt = subst Con (BoundaryTransparent≡.bnd≡≡ bt)

untransportCon≡
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : StrictHom.KernelHom≡ K K'}
  → BoundaryTransparent≡ h
  → Con (bnd K')
  → Con (bnd K)
untransportCon≡ bt = subst Con (sym (BoundaryTransparent≡.bnd≡≡ bt))

untransportCon-transportCon≡
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : StrictHom.KernelHom≡ K K'}
    (bt : BoundaryTransparent≡ h)
    (c : Con (bnd K))
  → untransportCon≡ bt (transportCon≡ bt c) ≡ c
untransportCon-transportCon≡ bt c =
  subst-sym-inv Con (BoundaryTransparent≡.bnd≡≡ bt) c

transportCon-untransportCon≡
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : StrictHom.KernelHom≡ K K'}
    (bt : BoundaryTransparent≡ h)
    (c : Con (bnd K'))
  → transportCon≡ bt (untransportCon≡ bt c) ≡ c
transportCon-untransportCon≡ bt c with BoundaryTransparent≡.bnd≡≡ bt
... | refl = refl
