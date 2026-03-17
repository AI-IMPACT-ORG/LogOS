{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.DimReg where

-- Dimensional-regularisation boundary, in minimal refinement-first form.
--
-- This is intentionally *not* a full Laurent-series implementation.
-- Instead, it is the barebones gadget that already supports:
--
-- - threading an explicit “pole vs finite” split through interpretations, and
-- - using the split as a normalisation-condition carrier (scheme data).
--
-- Carrier: pairs (pole , finite).
-- - The second component is a finite-join prequantale value (diagram/product).
-- - The first component only tracks “divergence / counterterm context” by join.
--
-- This is the order-0 shadow of dim-reg: enough to express MS-like projection
-- and to hook into the CK shadow development without committing to subtraction.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder; Con; _⊑_; _≈_; refl⊑; _×CP_ )
open import LogOS.LT.Sup.FinSup using (FinSup)

open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)
open import LogOS.Ports.Valuation.Regularisation using (PoleSplit)

-- Product boundary (pole × finite).
DimRegBoundary
  : ∀ {ℓCon ℓRel : Level}
  → ConPreorder ℓCon ℓRel
  → ConPreorder ℓCon ℓRel
DimRegBoundary CP = CP ×CP CP

-- Finite joins on the product boundary (pointwise).
DimRegFinSup
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → FinSup CP
  → FinSup (DimRegBoundary CP)
DimRegFinSup {CP = CP} FS =
  record
    { _⊔ᶠ_ = λ (p₁ , f₁) (p₂ , f₂) → (FinSup._⊔ᶠ_ FS p₁ p₂ , FinSup._⊔ᶠ_ FS f₁ f₂)
    ; ⊥ᶠ = (FinSup.⊥ᶠ FS , FinSup.⊥ᶠ FS)
    ; ⊥ᶠ-least = λ (p , f) → (FinSup.⊥ᶠ-least FS p , FinSup.⊥ᶠ-least FS f)
    ; ⊔ᶠ-ub₁ = λ (p₁ , f₁) (p₂ , f₂) → (FinSup.⊔ᶠ-ub₁ FS p₁ p₂ , FinSup.⊔ᶠ-ub₁ FS f₁ f₂)
    ; ⊔ᶠ-ub₂ = λ (p₁ , f₁) (p₂ , f₂) → (FinSup.⊔ᶠ-ub₂ FS p₁ p₂ , FinSup.⊔ᶠ-ub₂ FS f₁ f₂)
    ; ⊔ᶠ-least =
        λ { (p₁ , f₁) } { (p₂ , f₂) } { (p₃ , f₃) } (p₁≤p₃ , f₁≤f₃) (p₂≤p₃ , f₂≤f₃) →
          ( FinSup.⊔ᶠ-least FS p₁≤p₃ p₂≤p₃
          , FinSup.⊔ᶠ-least FS f₁≤f₃ f₂≤f₃
          )
    }

-- Join-prequantale on the product boundary:
-- - both components multiply pointwise (componentwise lifting).
--
-- This is deliberately conservative: it gives a low-friction carrier for
-- regularised evaluations plus an MS-like pole/finite *projector*, without
-- committing to Laurent-series convolution (which would require extra
-- combinatorics/termination machinery in `--safe`).
DimRegJoinPrequantale
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → JoinPrequantale CP
  → JoinPrequantale (DimRegBoundary CP)
DimRegJoinPrequantale {CP = CP} JP =
  record
    { FS = DimRegFinSup FS₀
    ; _·_ = _·ᴰ_
    ; e = (e₀ , e₀)
    ; ·-mono = ·ᴰ-mono
    ; ·-assoc≈ = ·ᴰ-assoc≈
    ; ·-idl≈ = ·ᴰ-idl≈
    ; ·-idr≈ = ·ᴰ-idr≈
    ; ·-distl-⊔ᶠ≈ = ·ᴰ-distl-⊔ᶠ≈
    ; ·-distr-⊔ᶠ≈ = ·ᴰ-distr-⊔ᶠ≈
    }
  where
    open JoinPrequantale JP renaming (_·_ to _·₀_; e to e₀)

    FS₀ : FinSup CP
    FS₀ = FS

    open FinSup (DimRegFinSup FS₀)
    _·ᴰ_ : Con (DimRegBoundary CP) → Con (DimRegBoundary CP) → Con (DimRegBoundary CP)
    (p₁ , f₁) ·ᴰ (p₂ , f₂) = (p₁ ·₀ p₂ , f₁ ·₀ f₂)

    ·ᴰ-mono
      : ∀ {a b c d}
      → _⊑_ (DimRegBoundary CP) a b
      → _⊑_ (DimRegBoundary CP) c d
      → _⊑_ (DimRegBoundary CP) (a ·ᴰ c) (b ·ᴰ d)
    ·ᴰ-mono {a = (p₁ , f₁)} {b = (p₁' , f₁')} {c = (p₂ , f₂)} {d = (p₂' , f₂')} (p₁≤p₁' , f₁≤f₁') (p₂≤p₂' , f₂≤f₂') =
      ( ·-mono p₁≤p₁' p₂≤p₂'
      , ·-mono f₁≤f₁' f₂≤f₂'
      )

    ·ᴰ-assoc≈
      : ∀ a b c
      → _≈_ (DimRegBoundary CP) ((a ·ᴰ b) ·ᴰ c) (a ·ᴰ (b ·ᴰ c))
    ·ᴰ-assoc≈ (p₁ , f₁) (p₂ , f₂) (p₃ , f₃) =
      ( ( fst (·-assoc≈ p₁ p₂ p₃)
        , fst (·-assoc≈ f₁ f₂ f₃)
        )
      , ( snd (·-assoc≈ p₁ p₂ p₃)
        , snd (·-assoc≈ f₁ f₂ f₃)
        )
      )

    ·ᴰ-idl≈ : ∀ a → _≈_ (DimRegBoundary CP) ((e₀ , e₀) ·ᴰ a) a
    ·ᴰ-idl≈ (p , f) =
      ( ( fst (·-idl≈ p)
        , fst (·-idl≈ f)
        )
      , ( snd (·-idl≈ p)
        , snd (·-idl≈ f)
        )
      )

    ·ᴰ-idr≈ : ∀ a → _≈_ (DimRegBoundary CP) (a ·ᴰ (e₀ , e₀)) a
    ·ᴰ-idr≈ (p , f) =
      ( ( fst (·-idr≈ p)
        , fst (·-idr≈ f)
        )
      , ( snd (·-idr≈ p)
        , snd (·-idr≈ f)
        )
      )

    ·ᴰ-distl-⊔ᶠ≈
      : ∀ a b c
      → _≈_ (DimRegBoundary CP) (((a ⊔ᶠ b) ·ᴰ c)) ((a ·ᴰ c) ⊔ᶠ (b ·ᴰ c))
    ·ᴰ-distl-⊔ᶠ≈ (p₁ , f₁) (p₂ , f₂) (p₃ , f₃) =
      ( ( fst (·-distl-⊔ᶠ≈ p₁ p₂ p₃)
        , fst (·-distl-⊔ᶠ≈ f₁ f₂ f₃)
        )
      , ( snd (·-distl-⊔ᶠ≈ p₁ p₂ p₃)
        , snd (·-distl-⊔ᶠ≈ f₁ f₂ f₃)
        )
      )

    ·ᴰ-distr-⊔ᶠ≈
      : ∀ a b c
      → _≈_ (DimRegBoundary CP) (a ·ᴰ (b ⊔ᶠ c)) ((a ·ᴰ b) ⊔ᶠ (a ·ᴰ c))
    ·ᴰ-distr-⊔ᶠ≈ (p₁ , f₁) (p₂ , f₂) (p₃ , f₃) =
      ( ( fst (·-distr-⊔ᶠ≈ p₁ p₂ p₃)
        , fst (·-distr-⊔ᶠ≈ f₁ f₂ f₃)
        )
      , ( snd (·-distr-⊔ᶠ≈ p₁ p₂ p₃)
        , snd (·-distr-⊔ᶠ≈ f₁ f₂ f₃)
        )
      )

-- Pole/finite split (MS-like projector) on the product boundary.
--
-- This is independent of how you choose the multiplication; the split is a
-- refinement-first decomposition against the boundary join.
DimRegPoleSplit
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → (JP : JoinPrequantale CP)
  → PoleSplit (DimRegJoinPrequantale JP)
DimRegPoleSplit {CP = CP} JP =
    record
      { pole = λ (p , f) → (p , ⊥ᶠ₀)
      ; finite = λ (p , f) → (⊥ᶠ₀ , f)
      ; pole-mono = λ { (p₁ , f₁) } { (p₂ , f₂) } (p₁≤p₂ , f₁≤f₂) → (p₁≤p₂ , refl⊑ CP)
      ; finite-mono = λ { (p₁ , f₁) } { (p₂ , f₂) } (p₁≤p₂ , f₁≤f₂) → (refl⊑ CP , f₁≤f₂)
      ; pole-idem≈ = λ _ → (refl⊑ (DimRegBoundary CP) , refl⊑ (DimRegBoundary CP))
      ; finite-idem≈ = λ _ → (refl⊑ (DimRegBoundary CP) , refl⊑ (DimRegBoundary CP))
      ; split≈ =
            λ (p , f) →
            let
              module FSLocal₀ = LogOS.LT.Sup.FinSup.FinSupLocal FS₀
            in
            ( ( FinSup.⊔ᶠ-ub₁ FS₀ p ⊥ᶠ₀
              , FinSup.⊔ᶠ-ub₂ FS₀ ⊥ᶠ₀ f
              )
            , ( fst (FSLocal₀.⊔ᶠ-idr-⊥ᶠ≈ p)
              , fst (FSLocal₀.⊔ᶠ-idl-⊥ᶠ≈ f)
              )
            )
      }
  where
    open JoinPrequantale JP
    open FinSup FS
    FS₀ : FinSup CP
    FS₀ = FS

    ⊥ᶠ₀ : Con CP
    ⊥ᶠ₀ = ⊥ᶠ
