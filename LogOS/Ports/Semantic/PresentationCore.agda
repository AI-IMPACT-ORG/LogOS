{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.PresentationCore where

-- Kernel-independent “presentation/port” core:
-- a presentation provides Import/Export legs between a constraint language and
-- an external formula language, together with satisfaction equivalences.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

record PresentationC {ℓCtx ℓCon ℓForm ℓSat : Level}
                     (Ctx : Set ℓCtx)
                     (Con : Set ℓCon)
                     (SatC : Ctx → Con → Set ℓSat)
                     : Set (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓForm ⊔ ℓSat)) where
  field
    Form   : Set ℓForm
    SatF   : Ctx → Form → Set ℓSat
    Export : Con → Form
    SatC≈F : ∀ p c → SatC p c ↔ SatF p (Export c)

    Import : Form → Con
    SatF≈C : ∀ p φ → SatF p φ ↔ SatC p (Import φ)

  -- Observational equivalence induced by satisfaction.

  ObsEqC : Con → Con → Set _
  ObsEqC = Prop.ObsEqOn SatC

  ObsEqF : Form → Form → Set _
  ObsEqF = Prop.ObsEqOn SatF

  RespectsObsEqC : (Con → Con) → Set _
  RespectsObsEqC = Prop.RespectsObsEqOn SatC

  -- Round-trip laws (forced by the satisfaction equivalences).

  Export∘Import≈F
    : ∀ p (φ : Form)
    → SatF p φ ↔ SatF p (Export (Import φ))
  Export∘Import≈F p φ =
    Prop.↔-trans (SatF≈C p φ) (SatC≈F p (Import φ))

  Import∘Export≈C
    : ∀ p (c : Con)
    → SatC p c ↔ SatC p (Import (Export c))
  Import∘Export≈C p c =
    Prop.↔-trans (SatC≈F p c) (SatF≈C p (Export c))

  -- Lifting a constraint endomap through a port.

  Extend : (Con → Con) → Form → Form
  Extend F φ = Export (F (Import φ))

  Extend-respects-ObsEqF
    : ∀ (F : Con → Con)
    → RespectsObsEqC F
    → ∀ {φ ψ}
    → ObsEqF φ ψ
    → ObsEqF (Extend F φ) (Extend F ψ)
  Extend-respects-ObsEqF F extF {φ} {ψ} eq p =
    let
      imp≈ : ObsEqC (Import φ) (Import ψ)
      imp≈ q =
        Prop.↔-trans
          (Prop.↔-sym (SatF≈C q φ))
          (Prop.↔-trans (eq q) (SatF≈C q ψ))

      satF→satC : SatF p (Extend F φ) ↔ SatC p (F (Import φ))
      satF→satC = Prop.↔-sym (SatC≈F p (F (Import φ)))

      satC≈ : SatC p (F (Import φ)) ↔ SatC p (F (Import ψ))
      satC≈ = extF imp≈ p

      satC→satF : SatC p (F (Import ψ)) ↔ SatF p (Extend F ψ)
      satC→satF = SatC≈F p (F (Import ψ))
    in
    Prop.↔-trans satF→satC (Prop.↔-trans satC≈ satC→satF)

  Extend-id
    : ∀ p (φ : Form)
    → SatF p (Extend (λ x → x) φ) ↔ SatF p φ
  Extend-id p φ = Prop.↔-sym (Export∘Import≈F p φ)

  Extend-comp
    : ∀ (F G : Con → Con)
    → RespectsObsEqC F
    → ∀ p (φ : Form)
    → SatF p (Extend F (Extend G φ)) ↔ SatF p (Extend (λ x → F (G x)) φ)
  Extend-comp F G extF p φ =
    let
      SatF-Export : ∀ x → SatF p (Export x) ↔ SatC p x
      SatF-Export x = Prop.↔-sym (SatC≈F p x)

      -- Convert through SatC, use port roundtrip on constraints, then extensionality.
      lhs₀ : SatF p (Extend F (Extend G φ)) ↔ SatC p (F (Import (Extend G φ)))
      lhs₀ = SatF-Export (F (Import (Extend G φ)))

      imp-roundtrip : ObsEqC (Import (Extend G φ)) (G (Import φ))
      imp-roundtrip q =
        let c = G (Import φ)
        in Prop.↔-sym (Import∘Export≈C q c)

      lhs₁ : SatC p (F (Import (Extend G φ))) ↔ SatC p (F (G (Import φ)))
      lhs₁ = extF imp-roundtrip p

      rhs₀ : SatF p (Extend (λ x → F (G x)) φ) ↔ SatC p (F (G (Import φ)))
      rhs₀ = SatF-Export (F (G (Import φ)))
    in
    Prop.↔-trans (Prop.↔-trans lhs₀ lhs₁) (Prop.↔-sym rhs₀)

