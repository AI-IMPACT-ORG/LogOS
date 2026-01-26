{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Base.Signature.Hom where

-- ============================================================================
-- SIGNATURE MORPHISMS (STRUCTURE-PRESERVING)
--
-- A `SigHom Sig₁ Sig₂` maps the primitive carriers of the LogOS signature
-- (Iface/Cosp/∂Cosp) and preserves all primitive operations on-the-nose.
--
-- This is intentionally lightweight: it enables *reindexing* kernels along a
-- signature map without changing any existing kernel definitions.
-- ============================================================================

open import LogOS.Prelude
open import LogOS.Base.Signature

open import LogOS.Prelude as Eq using (refl; trans; cong; sym)

record SigHom {ℓ : Level} (Sig₁ Sig₂ : LogOSSignature ℓ) : Set (lsuc ℓ) where
  open LogOSSignature Sig₁ renaming
    ( Iface to Iface₁; Cosp to Cosp₁; ∂Cosp to ∂Cosp₁
    ; src to src₁; tgt to tgt₁; idC to idC₁; _∘C_ to _∘C₁_; _⊕C_ to _⊕C₁_; _⊗C_ to _⊗C₁_
    ; src∂ to src∂₁; tgt∂ to tgt∂₁; id∂ to id∂₁; _∘∂_ to _∘∂₁_; _⊕∂_ to _⊕∂₁_; _⊗∂_ to _⊗∂₁_
    ; from∂ to from∂₁; to∂ to to∂₁
    )
  open LogOSSignature Sig₂ renaming
    ( Iface to Iface₂; Cosp to Cosp₂; ∂Cosp to ∂Cosp₂
    ; src to src₂; tgt to tgt₂; idC to idC₂; _∘C_ to _∘C₂_; _⊕C_ to _⊕C₂_; _⊗C_ to _⊗C₂_
    ; src∂ to src∂₂; tgt∂ to tgt∂₂; id∂ to id∂₂; _∘∂_ to _∘∂₂_; _⊕∂_ to _⊕∂₂_; _⊗∂_ to _⊗∂₂_
    ; from∂ to from∂₂; to∂ to to∂₂
    )
  field
    mapIface  : Iface₁ → Iface₂
    mapCosp   : Cosp₁  → Cosp₂
    map∂Cosp  : ∂Cosp₁ → ∂Cosp₂

    -- Bulk operations
    src-pres  : ∀ w → mapIface (src₁ w) ≡ src₂ (mapCosp w)
    tgt-pres  : ∀ w → mapIface (tgt₁ w) ≡ tgt₂ (mapCosp w)
    idC-pres  : ∀ A → mapCosp (idC₁ A) ≡ idC₂ (mapIface A)
    ∘C-pres   : ∀ g f → mapCosp (g ∘C₁ f) ≡ (mapCosp g ∘C₂ mapCosp f)
    ⊕C-pres   : ∀ f g → mapCosp (f ⊕C₁ g) ≡ (mapCosp f ⊕C₂ mapCosp g)
    ⊗C-pres   : ∀ f g → mapCosp (f ⊗C₁ g) ≡ (mapCosp f ⊗C₂ mapCosp g)

    -- Boundary operations
    src∂-pres : ∀ w → mapIface (src∂₁ w) ≡ src∂₂ (map∂Cosp w)
    tgt∂-pres : ∀ w → mapIface (tgt∂₁ w) ≡ tgt∂₂ (map∂Cosp w)
    id∂-pres  : ∀ A → map∂Cosp (id∂₁ A) ≡ id∂₂ (mapIface A)
    ∘∂-pres   : ∀ g f → map∂Cosp (g ∘∂₁ f) ≡ (map∂Cosp g ∘∂₂ map∂Cosp f)
    ⊕∂-pres   : ∀ f g → map∂Cosp (f ⊕∂₁ g) ≡ (map∂Cosp f ⊕∂₂ map∂Cosp g)
    ⊗∂-pres   : ∀ f g → map∂Cosp (f ⊗∂₁ g) ≡ (map∂Cosp f ⊗∂₂ map∂Cosp g)

    -- Bulk/boundary maps
    from∂-pres : ∀ w → mapCosp (from∂₁ w) ≡ from∂₂ (map∂Cosp w)
    to∂-pres   : ∀ w → map∂Cosp (to∂₁ w) ≡ to∂₂ (mapCosp w)

idSigHom : ∀ {ℓ} (Sig : LogOSSignature ℓ) → SigHom Sig Sig
idSigHom Sig = record
  { mapIface  = λ A → A
  ; mapCosp   = λ w → w
  ; map∂Cosp  = λ w → w
  ; src-pres  = λ _ → refl
  ; tgt-pres  = λ _ → refl
  ; idC-pres  = λ _ → refl
  ; ∘C-pres   = λ _ _ → refl
  ; ⊕C-pres   = λ _ _ → refl
  ; ⊗C-pres   = λ _ _ → refl
  ; src∂-pres = λ _ → refl
  ; tgt∂-pres = λ _ → refl
  ; id∂-pres  = λ _ → refl
  ; ∘∂-pres   = λ _ _ → refl
  ; ⊕∂-pres   = λ _ _ → refl
  ; ⊗∂-pres   = λ _ _ → refl
  ; from∂-pres = λ _ → refl
  ; to∂-pres   = λ _ → refl
  }

composeSigHom
  : ∀ {ℓ} {Sig₁ Sig₂ Sig₃ : LogOSSignature ℓ}
    → SigHom Sig₁ Sig₂ → SigHom Sig₂ Sig₃ → SigHom Sig₁ Sig₃
composeSigHom σ τ = record
  { mapIface  = λ A → SigHom.mapIface τ (SigHom.mapIface σ A)
  ; mapCosp   = λ w → SigHom.mapCosp τ (SigHom.mapCosp σ w)
  ; map∂Cosp  = λ w → SigHom.map∂Cosp τ (SigHom.map∂Cosp σ w)
  ; src-pres  = λ w → trans (cong (SigHom.mapIface τ) (SigHom.src-pres σ w)) (SigHom.src-pres τ (SigHom.mapCosp σ w))
  ; tgt-pres  = λ w → trans (cong (SigHom.mapIface τ) (SigHom.tgt-pres σ w)) (SigHom.tgt-pres τ (SigHom.mapCosp σ w))
  ; idC-pres  = λ A → trans (cong (SigHom.mapCosp τ) (SigHom.idC-pres σ A)) (SigHom.idC-pres τ (SigHom.mapIface σ A))
  ; ∘C-pres   = λ g f →
                  trans (cong (SigHom.mapCosp τ) (SigHom.∘C-pres σ g f))
                        (SigHom.∘C-pres τ (SigHom.mapCosp σ g) (SigHom.mapCosp σ f))
  ; ⊕C-pres   = λ f g →
                  trans (cong (SigHom.mapCosp τ) (SigHom.⊕C-pres σ f g))
                        (SigHom.⊕C-pres τ (SigHom.mapCosp σ f) (SigHom.mapCosp σ g))
  ; ⊗C-pres   = λ f g →
                  trans (cong (SigHom.mapCosp τ) (SigHom.⊗C-pres σ f g))
                        (SigHom.⊗C-pres τ (SigHom.mapCosp σ f) (SigHom.mapCosp σ g))
  ; src∂-pres = λ w → trans (cong (SigHom.mapIface τ) (SigHom.src∂-pres σ w)) (SigHom.src∂-pres τ (SigHom.map∂Cosp σ w))
  ; tgt∂-pres = λ w → trans (cong (SigHom.mapIface τ) (SigHom.tgt∂-pres σ w)) (SigHom.tgt∂-pres τ (SigHom.map∂Cosp σ w))
  ; id∂-pres  = λ A → trans (cong (SigHom.map∂Cosp τ) (SigHom.id∂-pres σ A)) (SigHom.id∂-pres τ (SigHom.mapIface σ A))
  ; ∘∂-pres   = λ g f →
                  trans (cong (SigHom.map∂Cosp τ) (SigHom.∘∂-pres σ g f))
                        (SigHom.∘∂-pres τ (SigHom.map∂Cosp σ g) (SigHom.map∂Cosp σ f))
  ; ⊕∂-pres   = λ f g →
                  trans (cong (SigHom.map∂Cosp τ) (SigHom.⊕∂-pres σ f g))
                        (SigHom.⊕∂-pres τ (SigHom.map∂Cosp σ f) (SigHom.map∂Cosp σ g))
  ; ⊗∂-pres   = λ f g →
                  trans (cong (SigHom.map∂Cosp τ) (SigHom.⊗∂-pres σ f g))
                        (SigHom.⊗∂-pres τ (SigHom.map∂Cosp σ f) (SigHom.map∂Cosp σ g))
  ; from∂-pres = λ w →
      trans
        (cong (SigHom.mapCosp τ) (SigHom.from∂-pres σ w))
        (SigHom.from∂-pres τ (SigHom.map∂Cosp σ w))
  ; to∂-pres   = λ w →
      trans
        (cong (SigHom.map∂Cosp τ) (SigHom.to∂-pres σ w))
        (SigHom.to∂-pres τ (SigHom.mapCosp σ w))
  }

-- ============================================================================
-- SIGNATURE SPANS, COCONES, AND PUSHOUTS (UNIVERSAL LOGIC STORY)
--
-- We avoid function extensionality by using pointwise equality of `SigHom`.
-- These structures are intentionally lightweight: they fit the existing
-- reindexing and interlingua tooling without forcing extra laws on signatures.
-- ============================================================================

record SigHomEq {ℓ : Level}
                {Sig₁ Sig₂ : LogOSSignature ℓ}
                (σ τ : SigHom Sig₁ Sig₂)
                : Set (lsuc ℓ) where
  field
    mapIface≡ : ∀ A → SigHom.mapIface σ A ≡ SigHom.mapIface τ A
    mapCosp≡  : ∀ w → SigHom.mapCosp σ w ≡ SigHom.mapCosp τ w
    map∂Cosp≡ : ∀ w → SigHom.map∂Cosp σ w ≡ SigHom.map∂Cosp τ w

sigHomEq-refl
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ}
    (σ : SigHom Sig₁ Sig₂)
  → SigHomEq σ σ
sigHomEq-refl _ =
  record
    { mapIface≡ = λ _ → refl
    ; mapCosp≡  = λ _ → refl
    ; map∂Cosp≡ = λ _ → refl
    }

sigHomEq-sym
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ}
    {σ τ : SigHom Sig₁ Sig₂}
  → SigHomEq σ τ → SigHomEq τ σ
sigHomEq-sym eq =
  record
    { mapIface≡ = λ A → sym (SigHomEq.mapIface≡ eq A)
    ; mapCosp≡  = λ w → sym (SigHomEq.mapCosp≡ eq w)
    ; map∂Cosp≡ = λ w → sym (SigHomEq.map∂Cosp≡ eq w)
    }

sigHomEq-trans
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ}
    {σ τ υ : SigHom Sig₁ Sig₂}
  → SigHomEq σ τ → SigHomEq τ υ → SigHomEq σ υ
sigHomEq-trans eq₁ eq₂ =
  record
    { mapIface≡ = λ A →
        trans (SigHomEq.mapIface≡ eq₁ A) (SigHomEq.mapIface≡ eq₂ A)
    ; mapCosp≡  = λ w →
        trans (SigHomEq.mapCosp≡ eq₁ w) (SigHomEq.mapCosp≡ eq₂ w)
    ; map∂Cosp≡ = λ w →
        trans (SigHomEq.map∂Cosp≡ eq₁ w) (SigHomEq.map∂Cosp≡ eq₂ w)
    }

record SigSpan {ℓ : Level}
               (Sig₀ Sig₁ Sig₂ : LogOSSignature ℓ)
               : Set (lsuc ℓ) where
  field
    left  : SigHom Sig₀ Sig₁
    right : SigHom Sig₀ Sig₂

record SigCocone {ℓ : Level}
                 {Sig₀ Sig₁ Sig₂ : LogOSSignature ℓ}
                 (span : SigSpan Sig₀ Sig₁ Sig₂)
                 (SigX : LogOSSignature ℓ)
                 : Set (lsuc ℓ) where
  field
    inl : SigHom Sig₁ SigX
    inr : SigHom Sig₂ SigX
    commute
      : SigHomEq
          (composeSigHom (SigSpan.left span) inl)
          (composeSigHom (SigSpan.right span) inr)

record SigPushout {ℓ : Level}
                  {Sig₀ Sig₁ Sig₂ : LogOSSignature ℓ}
                  (span : SigSpan Sig₀ Sig₁ Sig₂)
                  : Set (lsuc ℓ) where
  field
    SigP   : LogOSSignature ℓ
    cocone : SigCocone span SigP
    ump
      : ∀ {SigX : LogOSSignature ℓ}
      → (c : SigCocone span SigX)
      → Σ (SigHom SigP SigX)
          (λ h →
            SigHomEq (composeSigHom (SigCocone.inl cocone) h) (SigCocone.inl c)
            × SigHomEq (composeSigHom (SigCocone.inr cocone) h) (SigCocone.inr c))

record SigCoproduct {ℓ : Level}
                    (Sig₁ Sig₂ : LogOSSignature ℓ)
                    : Set (lsuc ℓ) where
  field
    SigΣ : LogOSSignature ℓ
    inl  : SigHom Sig₁ SigΣ
    inr  : SigHom Sig₂ SigΣ
    ump
      : ∀ {SigX : LogOSSignature ℓ}
      → (f₁ : SigHom Sig₁ SigX)
      → (f₂ : SigHom Sig₂ SigX)
      → Σ (SigHom SigΣ SigX)
          (λ h →
            SigHomEq (composeSigHom inl h) f₁
            × SigHomEq (composeSigHom inr h) f₂)
