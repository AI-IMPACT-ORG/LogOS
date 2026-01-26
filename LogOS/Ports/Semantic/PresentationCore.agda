{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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

  -- Observational preorder induced by satisfaction.

  ObsLeC : Con → Con → Set _
  ObsLeC = Prop.ObsLeOn SatC

  ObsLeF : Form → Form → Set _
  ObsLeF = Prop.ObsLeOn SatF

  -- Consistent aliases: use Con/Form naming at call sites.

  ObsEqCon : Con → Con → Set _
  ObsEqCon = ObsEqC

  ObsEqForm : Form → Form → Set _
  ObsEqForm = ObsEqF

  ObsLeCon : Con → Con → Set _
  ObsLeCon = ObsLeC

  ObsLeForm : Form → Form → Set _
  ObsLeForm = ObsLeF

  RespectsObsEqC : (Con → Con) → Set _
  RespectsObsEqC = Prop.RespectsObsEqOn SatC

  RespectsObsEqF : (Form → Form) → Set _
  RespectsObsEqF F = ∀ {φ ψ} → ObsEqF φ ψ → ObsEqF (F φ) (F ψ)

  RespectsObsEqCon : (Con → Con) → Set _
  RespectsObsEqCon = RespectsObsEqC

  RespectsObsEqForm : (Form → Form) → Set _
  RespectsObsEqForm = RespectsObsEqF

  module ObsEqC-Kit where
    open Prop.ObsEqKit (Prop.obsEqKit SatC) public
  module ObsEqF-Kit where
    open Prop.ObsEqKit (Prop.obsEqKit SatF) public

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

  -- Imports/exports respect observational equivalence.

  Export-respects-ObsEqC
    : ∀ {c d}
    → ObsEqC c d
    → ObsEqF (Export c) (Export d)
  Export-respects-ObsEqC {c} {d} eq p =
    Prop.↔-trans
      (Prop.↔-sym (SatC≈F p c))
      (Prop.↔-trans (eq p) (SatC≈F p d))

  Import-respects-ObsEqF
    : ∀ {φ ψ}
    → ObsEqF φ ψ
    → ObsEqC (Import φ) (Import ψ)
  Import-respects-ObsEqF {φ} {ψ} eq p =
    Prop.↔-trans
      (Prop.↔-sym (SatF≈C p φ))
      (Prop.↔-trans (eq p) (SatF≈C p ψ))

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

  -- Endomap action on forms (Extend) packaged as a reusable structure.
  record ExtendAction : Set (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓForm ⊔ ℓSat)) where
    field
      act : (Con → Con) → Form → Form
      act-respects-ObsEqF : ∀ F → RespectsObsEqC F → RespectsObsEqF (act F)
      act-id : ∀ p φ → SatF p (act (λ x → x) φ) ↔ SatF p φ
      act-comp
        : ∀ (F G : Con → Con)
        → RespectsObsEqC F
        → ∀ p (φ : Form)
        → SatF p (act F (act G φ)) ↔ SatF p (act (λ x → F (G x)) φ)

  extendAction : ExtendAction
  extendAction =
    record
      { act = Extend
      ; act-respects-ObsEqF = Extend-respects-ObsEqF
      ; act-id = Extend-id
      ; act-comp = Extend-comp
      }

-- Semantic lens view: a presentation is a bidirectional lens between
-- boundary constraints and external syntax, with round-trip laws up to
-- satisfaction equivalence.

record LensKit {ℓCtx ℓCon ℓForm ℓSat : Level}
               (Ctx : Set ℓCtx)
               (Con : Set ℓCon)
               (SatC : Ctx → Con → Set ℓSat)
               : Set (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓForm ⊔ ℓSat)) where
  field
    Pres : PresentationC {ℓForm = ℓForm} Ctx Con SatC
  open PresentationC Pres public

  roundTripF : ∀ p (φ : Form) → SatF p φ ↔ SatF p (Export (Import φ))
  roundTripF = Export∘Import≈F

  roundTripC : ∀ p (c : Con) → SatC p c ↔ SatC p (Import (Export c))
  roundTripC = Import∘Export≈C

lensFromPresentation
  : ∀ {ℓCtx ℓCon ℓForm ℓSat}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    {SatC : Ctx → Con → Set ℓSat}
  → PresentationC {ℓForm = ℓForm} Ctx Con SatC
  → LensKit {ℓForm = ℓForm} Ctx Con SatC
lensFromPresentation P = record { Pres = P }

lensTranslate
  : ∀ {ℓCtx ℓCon ℓForm₁ ℓForm₂ ℓSat}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    {SatC : Ctx → Con → Set ℓSat}
    (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx Con SatC)
    (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx Con SatC)
  → PresentationC.Form P₁ → PresentationC.Form P₂
lensTranslate P₁ P₂ φ =
  PresentationC.Export P₂ (PresentationC.Import P₁ φ)

-- -----------------------------------------------------------------------------
-- Presentation homomorphisms (semantic translations between presentations).
-- -----------------------------------------------------------------------------

record PresentationHom
  {ℓCtx ℓCon ℓSat ℓForm₁ ℓForm₂ : Level}
  {Ctx : Set ℓCtx}
  {Con : Set ℓCon}
  {SatC : Ctx → Con → Set ℓSat}
  (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx Con SatC)
  (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx Con SatC)
  : Set (lsuc (ℓCtx ⊔ ℓSat ⊔ ℓForm₁ ⊔ ℓForm₂)) where
  private
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂
  field
    map : P1.Form → P2.Form
    sem : ∀ p φ → P1.SatF p φ ↔ P2.SatF p (map φ)

open PresentationHom public

PresentationHom-id
  : ∀ {ℓCtx ℓCon ℓSat ℓForm : Level}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    {SatC : Ctx → Con → Set ℓSat}
    (P : PresentationC {ℓForm = ℓForm} Ctx Con SatC)
  → PresentationHom P P
PresentationHom-id _ =
  record
    { map = λ φ → φ
    ; sem = λ _ _ → Prop.↔-refl
    }

PresentationHom-compose
  : ∀ {ℓCtx ℓCon ℓSat ℓForm₁ ℓForm₂ ℓForm₃ : Level}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    {SatC : Ctx → Con → Set ℓSat}
    {P₁ : PresentationC {ℓForm = ℓForm₁} Ctx Con SatC}
    {P₂ : PresentationC {ℓForm = ℓForm₂} Ctx Con SatC}
    {P₃ : PresentationC {ℓForm = ℓForm₃} Ctx Con SatC}
  → PresentationHom P₁ P₂
  → PresentationHom P₂ P₃
  → PresentationHom P₁ P₃
PresentationHom-compose h₁ h₂ =
  record
    { map = λ φ → map h₂ (map h₁ φ)
    ; sem = λ p φ →
        Prop.↔-trans (sem h₁ p φ) (sem h₂ p (map h₁ φ))
    }

PresentationHom-respects-ObsEq
  : ∀ {ℓCtx ℓCon ℓSat ℓForm₁ ℓForm₂ : Level}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    {SatC : Ctx → Con → Set ℓSat}
    {P₁ : PresentationC {ℓForm = ℓForm₁} Ctx Con SatC}
    {P₂ : PresentationC {ℓForm = ℓForm₂} Ctx Con SatC}
  → (h : PresentationHom P₁ P₂)
  → ∀ {φ ψ}
  → PresentationC.ObsEqF P₁ φ ψ
  → PresentationC.ObsEqF P₂ (map h φ) (map h ψ)
PresentationHom-respects-ObsEq {P₁ = P₁} {P₂ = P₂} h {φ} {ψ} eq p =
  let
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂
  in
  Prop.↔-trans
    (Prop.↔-sym (sem h p φ))
    (Prop.↔-trans (eq p) (sem h p ψ))
