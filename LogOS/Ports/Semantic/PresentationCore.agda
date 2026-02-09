{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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

import LogOS.Minimal.RelPreorder as RP
import LogOS.Minimal.View as View

-- Satisfaction-based “system” interface.
--
-- A `SatSystem` is the common denominator of the ports/adapters spine:
--   - contexts (`Ctx`) as observers/environments,
--   - constraints (`Con`) as boundary claims,
--   - satisfaction (`Sat`) as communicable meaning.

record SatSystem {ℓCtx ℓCon ℓSat : Level}
  : Set (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓSat)) where
  field
    Ctx : Set ℓCtx
    Con : Set ℓCon
    Sat : Ctx → Con → Set ℓSat

  -- Observational relations induced by satisfaction (no antisymmetry assumed).
  ObsEq : Con → Con → Set (ℓCtx ⊔ ℓSat)
  ObsEq = Prop.ObsEqOn Sat

  ObsLe : Con → Con → Set (ℓCtx ⊔ ℓSat)
  ObsLe = Prop.ObsLeOn Sat

  -- Observational preorder as a first-class view target.
  --
  -- This keeps the universe levels honest: the carrier lives in `ℓCon`, but the
  -- observational relation lives in `ℓCtx ⊔ ℓSat`.
  ObsRP : RP.RelPreorder ℓCon (ℓCtx ⊔ ℓSat)
  ObsRP = View.ObsPreorder Sat

  -- Observational mutual refinement (two-way observation implication).
  Obs≈ : Con → Con → Set (ℓCtx ⊔ ℓSat)
  Obs≈ = View.Obs≈ Sat

  ObsEq↔Obs≈ : ∀ {x y} → ObsEq x y ↔ Obs≈ x y
  ObsEq↔Obs≈ {x} {y} = View.ObsEqOn↔Obs≈ Sat {x = x} {y = y}

  RespectsObsEq : (Con → Con) → Set (ℓCtx ⊔ ℓCon ⊔ ℓSat)
  RespectsObsEq = Prop.RespectsObsEqOn Sat

  -- Canonical notion: extensionality w.r.t. observational mutual refinement.
  RespectsObs≈ : (Con → Con) → Set (ℓCtx ⊔ ℓCon ⊔ ℓSat)
  RespectsObs≈ F = ∀ {x y} → Obs≈ x y → Obs≈ (F x) (F y)

  RespectsObsEq↔RespectsObs≈ : ∀ {F} → RespectsObsEq F ↔ RespectsObs≈ F
  RespectsObsEq↔RespectsObs≈ {F} =
    Prop.intro
      (λ ext {x} {y} xy≈ →
        Prop._↔_.to (ObsEq↔Obs≈ {x = F x} {y = F y})
          (ext (Prop._↔_.from (ObsEq↔Obs≈ {x = x} {y = y}) xy≈)))
      (λ ext {x} {y} xyEq →
        Prop._↔_.from (ObsEq↔Obs≈ {x = F x} {y = F y})
          (ext (Prop._↔_.to (ObsEq↔Obs≈ {x = x} {y = y}) xyEq)))

  module ObsEq-Kit where
    open Prop.ObsEqKit (Prop.obsEqKit Sat) public

private
  mkSatSystem
    : ∀ {ℓCtx ℓCon ℓSat : Level}
    → (Ctxₛ : Set ℓCtx)
    → (Conₛ : Set ℓCon)
    → (Satₛ : Ctxₛ → Conₛ → Set ℓSat)
    → SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}
  mkSatSystem Ctxₛ Conₛ Satₛ =
    record
      { Ctx = Ctxₛ
      ; Con = Conₛ
      ; Sat = Satₛ
      }

-- Preferred constructor surface: use `satSystem` (from this module) rather than
-- calling `mkSatSystem` directly elsewhere. This keeps SatSystem construction
-- trivial to audit: search for `satSystem` call sites and inspect only this
-- wrapper if the representation ever changes.

satSystem
  : ∀ {ℓCtx ℓCon ℓSat : Level}
  → (Ctxₛ : Set ℓCtx)
  → (Conₛ : Set ℓCon)
  → (Satₛ : Ctxₛ → Conₛ → Set ℓSat)
  → SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}
satSystem = mkSatSystem

record PresentationC {ℓCtx ℓCon ℓForm ℓSat : Level}
                     (S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat})
                     : Set (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓForm ⊔ ℓSat)) where
  open SatSystem S public renaming (Sat to SatC)
  field
    Form   : Set ℓForm
    SatF   : Ctx → Form → Set ℓSat
    Export : Con → Form
    SatC≈F : ∀ p c → SatC p c ↔ SatF p (Export c)

    Import : Form → Con
    SatF≈C : ∀ p φ → SatF p φ ↔ SatC p (Import φ)

  -- Observational equality induced by satisfaction.

  ObsEqC : Con → Con → Set _
  ObsEqC = Prop.ObsEqOn SatC

  ObsEqF : Form → Form → Set _
  ObsEqF = Prop.ObsEqOn SatF

  -- Observational preorder induced by satisfaction.

  ObsLeC : Con → Con → Set _
  ObsLeC = Prop.ObsLeOn SatC

  ObsLeF : Form → Form → Set _
  ObsLeF = Prop.ObsLeOn SatF

  -- Observational preorders as first-class view targets.
  ObsRPC : RP.RelPreorder ℓCon (ℓCtx ⊔ ℓSat)
  ObsRPC = View.ObsPreorder SatC

  ObsRPF : RP.RelPreorder ℓForm (ℓCtx ⊔ ℓSat)
  ObsRPF = View.ObsPreorder SatF

  Obs≈C : Con → Con → Set _
  Obs≈C = View.Obs≈ SatC

  Obs≈F : Form → Form → Set _
  Obs≈F = View.Obs≈ SatF

  ObsEqC↔Obs≈C : ∀ {x y} → ObsEqC x y ↔ Obs≈C x y
  ObsEqC↔Obs≈C {x} {y} = View.ObsEqOn↔Obs≈ SatC {x = x} {y = y}

  ObsEqF↔Obs≈F : ∀ {x y} → ObsEqF x y ↔ Obs≈F x y
  ObsEqF↔Obs≈F {x} {y} = View.ObsEqOn↔Obs≈ SatF {x = x} {y = y}

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

  -- Canonical notion: extensionality w.r.t. observational mutual refinement.
  RespectsObs≈C : (Con → Con) → Set _
  RespectsObs≈C F = ∀ {c d} → Obs≈C c d → Obs≈C (F c) (F d)

  RespectsObs≈F : (Form → Form) → Set _
  RespectsObs≈F F = ∀ {φ ψ} → Obs≈F φ ψ → Obs≈F (F φ) (F ψ)

  RespectsObsEqC↔RespectsObs≈C : ∀ {F} → RespectsObsEqC F ↔ RespectsObs≈C F
  RespectsObsEqC↔RespectsObs≈C {F} =
    Prop.intro
      (λ ext {c} {d} cd≈ →
        Prop._↔_.to (ObsEqC↔Obs≈C {x = F c} {y = F d})
          (ext (Prop._↔_.from (ObsEqC↔Obs≈C {x = c} {y = d}) cd≈)))
      (λ ext {c} {d} cdEq →
        Prop._↔_.from (ObsEqC↔Obs≈C {x = F c} {y = F d})
          (ext (Prop._↔_.to (ObsEqC↔Obs≈C {x = c} {y = d}) cdEq)))

  RespectsObsEqF↔RespectsObs≈F : ∀ {F} → RespectsObsEqF F ↔ RespectsObs≈F F
  RespectsObsEqF↔RespectsObs≈F {F} =
    Prop.intro
      (λ ext {φ} {ψ} eq≈ →
        Prop._↔_.to (ObsEqF↔Obs≈F {x = F φ} {y = F ψ})
          (ext (Prop._↔_.from (ObsEqF↔Obs≈F {x = φ} {y = ψ}) eq≈)))
      (λ ext {φ} {ψ} eqEq →
        Prop._↔_.from (ObsEqF↔Obs≈F {x = F φ} {y = F ψ})
          (ext (Prop._↔_.to (ObsEqF↔Obs≈F {x = φ} {y = ψ}) eqEq)))

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

  -- Imports/exports respect observational equality.

  Export-respects-ObsEqC
    : ∀ {c d}
    → ObsEqC c d
    → ObsEqF (Export c) (Export d)
  Export-respects-ObsEqC {c} {d} eq p =
    Prop.↔-trans
      (Prop.↔-sym (SatC≈F p c))
      (Prop.↔-trans (eq p) (SatC≈F p d))

  -- Derived: `Export` also respects mutual refinement (the canonical `≈`-shaped form).
  Export-respects-Obs≈C
    : ∀ {c d}
    → Obs≈C c d
    → Obs≈F (Export c) (Export d)
  Export-respects-Obs≈C {c} {d} eq≈ =
    Prop._↔_.to (ObsEqF↔Obs≈F {x = Export c} {y = Export d})
      (Export-respects-ObsEqC (Prop._↔_.from (ObsEqC↔Obs≈C {x = c} {y = d}) eq≈))

  Import-respects-ObsEqF
    : ∀ {φ ψ}
    → ObsEqF φ ψ
    → ObsEqC (Import φ) (Import ψ)
  Import-respects-ObsEqF {φ} {ψ} eq p =
    Prop.↔-trans
      (Prop.↔-sym (SatF≈C p φ))
      (Prop.↔-trans (eq p) (SatF≈C p ψ))

  -- Derived: `Import` also respects mutual refinement (the canonical `≈`-shaped form).
  Import-respects-Obs≈F
    : ∀ {φ ψ}
    → Obs≈F φ ψ
    → Obs≈C (Import φ) (Import ψ)
  Import-respects-Obs≈F {φ} {ψ} eq≈ =
    Prop._↔_.to (ObsEqC↔Obs≈C {x = Import φ} {y = Import ψ})
      (Import-respects-ObsEqF (Prop._↔_.from (ObsEqF↔Obs≈F {x = φ} {y = ψ}) eq≈))

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

  -- Derived: lifting also respects mutual refinement (the canonical `≈`-shaped form).
  Extend-respects-Obs≈F
    : ∀ (F : Con → Con)
    → RespectsObs≈C F
    → ∀ {φ ψ}
    → Obs≈F φ ψ
    → Obs≈F (Extend F φ) (Extend F ψ)
  Extend-respects-Obs≈F F extF≈ {φ} {ψ} eq≈ =
    Prop._↔_.to (ObsEqF↔Obs≈F {x = Extend F φ} {y = Extend F ψ})
      (Extend-respects-ObsEqF F
        (Prop._↔_.from (RespectsObsEqC↔RespectsObs≈C {F = F}) extF≈)
        (Prop._↔_.from (ObsEqF↔Obs≈F {x = φ} {y = ψ}) eq≈))

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
               (S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat})
               : Set (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓForm ⊔ ℓSat)) where
  field
    Pres : PresentationC {ℓForm = ℓForm} S
  open PresentationC Pres public

  roundTripF : ∀ p (φ : Form) → SatF p φ ↔ SatF p (Export (Import φ))
  roundTripF = Export∘Import≈F

  roundTripC : ∀ p (c : Con) → SatC p c ↔ SatC p (Import (Export c))
  roundTripC = Import∘Export≈C

lensFromPresentation
  : ∀ {ℓCtx ℓCon ℓForm ℓSat}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
  → PresentationC {ℓForm = ℓForm} S
  → LensKit {ℓForm = ℓForm} S
lensFromPresentation P = record { Pres = P }

lensTranslate
  : ∀ {ℓCtx ℓCon ℓForm₁ ℓForm₂ ℓSat}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    (P₁ : PresentationC {ℓForm = ℓForm₁} S)
    (P₂ : PresentationC {ℓForm = ℓForm₂} S)
  → PresentationC.Form P₁ → PresentationC.Form P₂
lensTranslate P₁ P₂ φ =
  PresentationC.Export P₂ (PresentationC.Import P₁ φ)

-- -----------------------------------------------------------------------------
-- Presentation homomorphisms (semantic translations between presentations).
-- -----------------------------------------------------------------------------

record PresentationHom
  {ℓCtx ℓCon ℓSat ℓForm₁ ℓForm₂ : Level}
  {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
  (P₁ : PresentationC {ℓForm = ℓForm₁} S)
  (P₂ : PresentationC {ℓForm = ℓForm₂} S)
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
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    (P : PresentationC {ℓForm = ℓForm} S)
  → PresentationHom P P
PresentationHom-id _ =
  record
    { map = λ φ → φ
    ; sem = λ _ _ → Prop.↔-refl
    }

PresentationHom-compose
  : ∀ {ℓCtx ℓCon ℓSat ℓForm₁ ℓForm₂ ℓForm₃ : Level}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    {P₁ : PresentationC {ℓForm = ℓForm₁} S}
    {P₂ : PresentationC {ℓForm = ℓForm₂} S}
    {P₃ : PresentationC {ℓForm = ℓForm₃} S}
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
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    {P₁ : PresentationC {ℓForm = ℓForm₁} S}
    {P₂ : PresentationC {ℓForm = ℓForm₂} S}
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

-- Derived: `PresentationHom` also respects mutual refinement (the canonical `≈`-shaped form).
PresentationHom-respects-Obs≈F
  : ∀ {ℓCtx ℓCon ℓSat ℓForm₁ ℓForm₂ : Level}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    {P₁ : PresentationC {ℓForm = ℓForm₁} S}
    {P₂ : PresentationC {ℓForm = ℓForm₂} S}
  → (h : PresentationHom P₁ P₂)
  → ∀ {φ ψ}
  → PresentationC.Obs≈F P₁ φ ψ
  → PresentationC.Obs≈F P₂ (map h φ) (map h ψ)
PresentationHom-respects-Obs≈F {P₁ = P₁} {P₂ = P₂} h {φ} {ψ} eq =
  let
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂
  in
  Prop._↔_.to (P2.ObsEqF↔Obs≈F {x = map h φ} {y = map h ψ})
    (PresentationHom-respects-ObsEq {P₁ = P₁} {P₂ = P₂} h
      (Prop._↔_.from (P1.ObsEqF↔Obs≈F {x = φ} {y = ψ}) eq))
