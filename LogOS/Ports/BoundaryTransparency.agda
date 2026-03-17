{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.BoundaryTransparency where

-- “Adapters are pure wiring” as a named port.
--
-- A `KernelHom K K'` may transport boundary constraints via `map∂ : Con (bnd K) → Con (bnd K')`.
-- In many settings we want boundary *transparency*: the boundary is “the same” on both sides
-- (possibly up to judgmental equality), and the adapter does not change constraints—only code.
--
-- Since boundaries can be propositionally equal without being judgmental, we package:
-- - a boundary identification `bnd≡ : bnd K ≡ bnd K'`, and
-- - a refinement-level certificate that `map∂` agrees with transport along that
--   identification.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _≈_; ≡→≈)
open import LogOS.LT.Kernel using (Kernel; bnd; decode)
open import LogOS.LT.Hom.Core using
  ( KernelHom
  ; map∂
  ; map∂-mono
  ; mapCode
  ; decode-mapCode≈
  ; idKernelHom
  ; _∘_
  )

record BoundaryTransparent
  {ℓ ℓRel ℓCode ℓCode' : Level}
  {K : Kernel ℓ ℓRel ℓCode}
  {K' : Kernel ℓ ℓRel ℓCode'}
  (h : KernelHom K K') : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode ⊔ ℓCode')) where
  field
    bnd≡ : bnd K ≡ bnd K'
    map∂-transparent≈ : ∀ c → _≈_ (bnd K') (map∂ h c) (subst Con bnd≡ c)

  decode-mapCode-transparent
    : ∀ γ → _≈_ (bnd K') (decode K' (mapCode h γ)) (subst Con bnd≡ (decode K γ))
  decode-mapCode-transparent γ =
    let
      module R = LogOS.Prelude.RefinementKit.Reasoning (bnd K')
      open R using (begin≈_; _≈⟨_⟩_; _∎≈)
    in
    begin≈
      decode K' (mapCode h γ) ≈⟨ decode-mapCode≈ h γ ⟩
      map∂ h (decode K γ) ≈⟨ map∂-transparent≈ (decode K γ) ⟩
      subst Con bnd≡ (decode K γ) ∎≈

open BoundaryTransparent public

-- --------------------------------------------------------------------------
-- Small helpers: boundary transport as a named operation.

transportCon
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : KernelHom K K'}
  → BoundaryTransparent h
  → Con (bnd K)
  → Con (bnd K')
transportCon bt = subst Con (BoundaryTransparent.bnd≡ bt)

untransportCon
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : KernelHom K K'}
  → BoundaryTransparent h
  → Con (bnd K')
  → Con (bnd K)
untransportCon bt = subst Con (sym (BoundaryTransparent.bnd≡ bt))

-- Refinement-first bridges: boundary transparency yields mutual refinement.
--
-- These lemmas avoid forcing downstream developments to rewrite by strict
-- equalities when they only need behavioral equivalence (`≈`).

decode-mapCode-transparent≈
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : KernelHom K K'}
  → (bt : BoundaryTransparent h)
  → ∀ γ
  → _≈_ (bnd K') (decode K' (mapCode h γ)) (transportCon bt (decode K γ))
decode-mapCode-transparent≈ {K' = K'} bt γ =
  BoundaryTransparent.decode-mapCode-transparent bt γ

transportCon≈
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : KernelHom K K'}
  → (bt : BoundaryTransparent h)
  → ∀ {x y}
  → _≈_ (bnd K) x y
  → _≈_ (bnd K') (transportCon bt x) (transportCon bt y)
transportCon≈ bt xy with bnd≡ bt
... | refl = xy

untransportCon≈
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : KernelHom K K'}
  → (bt : BoundaryTransparent h)
  → ∀ {x y}
  → _≈_ (bnd K') x y
  → _≈_ (bnd K) (untransportCon bt x) (untransportCon bt y)
untransportCon≈ bt xy with bnd≡ bt
... | refl = xy

untransport-map∂-transparent≈
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : KernelHom K K'}
  → (bt : BoundaryTransparent h)
  → ∀ c
  → _≈_ (bnd K) (untransportCon bt (map∂ h c)) c
untransport-map∂-transparent≈ {K = K} {h = h} bt c =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning (bnd K)
    open R using (begin≈_; _≈⟨_⟩_; _∎≈)
  in
  begin≈
    untransportCon bt (map∂ h c)
      ≈⟨ untransportCon≈ bt (map∂-transparent≈ bt c) ⟩
    untransportCon bt (transportCon bt c)
      ≈⟨ ≡→≈ {CP = bnd K} (subst-sym-inv Con (bnd≡ bt) c) ⟩
    c ∎≈

untransport-decode-mapCode-transparent≈
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : KernelHom K K'}
  → (bt : BoundaryTransparent h)
  → ∀ γ
  → _≈_ (bnd K) (untransportCon bt (decode K' (mapCode h γ))) (decode K γ)
untransport-decode-mapCode-transparent≈ {K = K} {K' = K'} {h = h} bt γ =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning (bnd K)
    open R using (begin≈_; _≈⟨_⟩_; _∎≈)
  in
  begin≈
    untransportCon bt (decode K' (mapCode h γ))
      ≈⟨ untransportCon≈ bt (decode-mapCode-transparent bt γ) ⟩
    untransportCon bt (transportCon bt (decode K γ))
      ≈⟨ ≡→≈ {CP = bnd K} (subst-sym-inv Con (bnd≡ bt) (decode K γ)) ⟩
    decode K γ ∎≈

untransportCon-transportCon
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : KernelHom K K'}
    (bt : BoundaryTransparent h)
    (c : Con (bnd K))
  → untransportCon bt (transportCon bt c) ≡ c
untransportCon-transportCon bt c =
  subst-sym-inv Con (BoundaryTransparent.bnd≡ bt) c

transportCon-untransportCon
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h : KernelHom K K'}
    (bt : BoundaryTransparent h)
    (c : Con (bnd K'))
  → transportCon bt (untransportCon bt c) ≡ c
transportCon-untransportCon bt c with BoundaryTransparent.bnd≡ bt
... | refl = refl

-- Convenience: identity wiring is boundary-transparent by definition.
idBoundaryTransparent
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → BoundaryTransparent (idKernelHom K)
idBoundaryTransparent {K = K} =
  record
    { bnd≡ = refl
    ; map∂-transparent≈ = λ _ → ≡→≈ {CP = bnd K} refl
    }

-- Convenience: pure wiring composes (boundary transport composes).
compBoundaryTransparent
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
    {f : KernelHom K₁ K₂}
    {g : KernelHom K₂ K₃}
  → BoundaryTransparent f
  → BoundaryTransparent g
  → BoundaryTransparent (g ∘ f)
compBoundaryTransparent {K₃ = K₃} {f = f} {g = g} tf tg =
  record
    { bnd≡ = trans (bnd≡ tf) (bnd≡ tg)
    ; map∂-transparent≈ = λ c →
        let
          module R = LogOS.Prelude.RefinementKit.Reasoning (bnd K₃)
          open R using (begin≈_; _≈⟨_⟩_; _∎≈)
        in
        begin≈
          map∂ g (map∂ f c)
            ≈⟨ ( map∂-mono g (fst (map∂-transparent≈ tf c))
               , map∂-mono g (snd (map∂-transparent≈ tf c))
               ) ⟩
          map∂ g (transportCon tf c)
            ≈⟨ map∂-transparent≈ tg (transportCon tf c) ⟩
          transportCon tg (transportCon tf c)
            ≈⟨ ≡→≈ {CP = bnd K₃} (sym (subst-trans Con (bnd≡ tf) (bnd≡ tg) c)) ⟩
          subst Con (trans (bnd≡ tf) (bnd≡ tg)) c ∎≈
    }
