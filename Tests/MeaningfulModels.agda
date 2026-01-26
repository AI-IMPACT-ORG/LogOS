{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.MeaningfulModels where

-- Concrete witnesses that the repository’s vacuity guards are satisfiable.
--
-- Goal: show that the various “meaningfulness” guard records are not empty
-- by constructing a tiny explicit model with genuinely nontrivial boundary
-- satisfaction (not everything satisfied, not everything unsatisfied).

open import LogOS.Prelude
open import LogOS.Prelude.Bool using (Bool; true; false)
open import LogOS.Syntax.Prop using (¬_; ⊥; ⊥-elim; _↔_; intro)

open import LogOS.Base.Sorts as Sorts
open import LogOS.Base.Ops.Cospan as Cosp
open import LogOS.Base.Ops.Boundary as Bnd
open import LogOS.Base.Signature using (LogOSSignature)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Minimal.Adjunction using (MonoidalOps; LaxMonoidalAdjunction)
open import LogOS.Minimal.World as Worlds
import LogOS.Minimal.Truth as Truth

open import LogOS.QAdapters.QNatMul using (QNatMul)
import LogOS.QAdapters.Guards as QGuards

open import LogOS.Kernel.Core as Core
import LogOS.Kernel.LogicKernel as LK
import LogOS.Kernel.LogicKernel.Boundary as LKBoundary
import LogOS.Kernel.LogicKernel.VacuityGuards as LKVac

open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.Semantics using (BoundarySemantics)
open import LogOS.Boundary.Port using (BoundaryPort)
import LogOS.Ports.Semantic.VacuityGuards as PortVac
open import LogOS.Ports.Semantic.Interoperability using (PortAdapter)

-- --------------------------------------------------------------------------
-- A tiny signature
-- --------------------------------------------------------------------------

Sig₀ : LogOSSignature lzero
Sig₀ =
  record
    { sorts =
        record
          { Iface = ⊤
          ; Cosp  = ⊤
          ; ∂Cosp = ⊤
          }
    ; cospanOps =
        record
          { src  = λ _ → tt
          ; tgt  = λ _ → tt
          ; idC  = λ _ → tt
          ; _∘C_ = λ _ _ → tt
          ; _⊕C_ = λ _ _ → tt
          ; _⊗C_ = λ _ _ → tt
          }
    ; boundaryOps =
        record
          { src∂  = λ _ → tt
          ; tgt∂  = λ _ → tt
          ; id∂   = λ _ → tt
          ; _∘∂_  = λ _ _ → tt
          ; _⊕∂_  = λ _ _ → tt
          ; _⊗∂_  = λ _ _ → tt
          ; from∂ = λ _ → tt
          ; to∂   = λ _ → tt
          }
    }

-- Avoid opening `Cosp`/`∂Cosp` unqualified: `Cosp` is also a projection name from `Sorts`.

-- --------------------------------------------------------------------------
-- Boolean boundary constraints with a standard preorder (false ≤ true)
-- --------------------------------------------------------------------------

infix 4 _⊑ᵇ_
_⊑ᵇ_ : Bool → Bool → Set lzero
false ⊑ᵇ _     = ⊤
true  ⊑ᵇ true  = ⊤
true  ⊑ᵇ false = ⊥

⊑ᵇ-refl : ∀ {b} → b ⊑ᵇ b
⊑ᵇ-refl {false} = tt
⊑ᵇ-refl {true}  = tt

⊑ᵇ-trans : ∀ {a b c} → a ⊑ᵇ b → b ⊑ᵇ c → a ⊑ᵇ c
⊑ᵇ-trans {false} {_} {_} _ _ = tt
⊑ᵇ-trans {true}  {false} {_} ab _ = ⊥-elim ab
⊑ᵇ-trans {true}  {true}  {_} _ bc = bc

BoolPreorder : ConPreorder lzero
BoolPreorder =
  record
    { Con   = Bool
    ; _⊑_   = _⊑ᵇ_
    ; refl  = ⊑ᵇ-refl
    ; trans = ⊑ᵇ-trans
    }

BB₀ : BulkBoundary lzero
BB₀ = record { bulk = BoolPreorder ; bnd = BoolPreorder }

-- --------------------------------------------------------------------------
-- Trivial monoidal ops + trivial lax monoidal adjunction (identity maps)
-- --------------------------------------------------------------------------

Mᵇ : MonoidalOps BoolPreorder
Mᵇ =
  record
    { _⊗_   = λ x _ → x
    ; I     = false
    ; mono⊗ = λ x≤x' _ → x≤x'
    }

I-refl : _⊑ᵇ_ false false
I-refl = tt

Holo₀ : LaxMonoidalAdjunction BB₀ Mᵇ Mᵇ
Holo₀ =
  record
    { core =
        record
          { ext        = λ c → c
          ; bnd        = λ c → c
          ; unit-lax   = λ c → ⊑ᵇ-refl {b = c}
          ; counit-lax = λ c → ⊑ᵇ-refl {b = c}
          }
    ; ext-⊗-lax = λ x _ → ⊑ᵇ-refl {b = x}
    ; ext-I-lax = I-refl
    ; bnd-⊗-lax = λ x _ → ⊑ᵇ-refl {b = x}
    ; bnd-I-lax = I-refl
    }

-- --------------------------------------------------------------------------
-- World + truth layers
-- --------------------------------------------------------------------------

W₀ : Worlds.WorldH Sig₀ QNatMul
W₀ =
  record
    { _≤ctx_ = λ _ _ → ⊤
    ; WFlow  = λ _ _ → QAdapter.e QNatMul
    ; wflow-refl  = λ _ → QAdapter.≤s-refl QNatMul
    ; wflow-trans = λ _ _ _ →
        subst
          (λ x → QAdapter._≤s_ QNatMul x (QAdapter.e QNatMul))
          (QAdapter.·-idr QNatMul (QAdapter.e QNatMul))
          (QAdapter.≤s-refl QNatMul)
    }

module HT₀ = Truth.HomotypicalTruth Sig₀ QNatMul W₀

SatBool : Bool → Set lzero
SatBool true  = ⊤
SatBool false = ⊥

Sat_H₀ : LogOSSignature.Cosp Sig₀ → Bool → Set lzero
Sat_H₀ _ c = SatBool c

mono-Con₀
  : ∀ {w : LogOSSignature.Cosp Sig₀} {c c' : Bool}
  → BulkBoundary._⊑bnd_ BB₀ c c'
  → Sat_H₀ w c
  → Sat_H₀ w c'
mono-Con₀ {c = false} {_} _ sat = ⊥-elim sat
mono-Con₀ {c = true} {c' = true} _ sat = sat
mono-Con₀ {c = true} {c' = false} c≤c' _ = ⊥-elim c≤c'

mono-ctx₀
  : ∀ {w w' : LogOSSignature.Cosp Sig₀} {c : Bool}
  → Worlds.WorldH._≤ctx_ W₀ w w'
  → Sat_H₀ w c
  → Sat_H₀ w' c
mono-ctx₀ _ sat = sat

HTruth₀ : HT₀.HLayer BB₀
HTruth₀ =
  record
    { Sat_H = Sat_H₀
    ; mono-Con = λ {w} {c} {c'} le sat → mono-Con₀ {w = w} {c = c} {c' = c'} le sat
    ; mono-ctx = λ {w} {w'} {c} w≤ sat → mono-ctx₀ {w = w} {w' = w'} {c = c} w≤ sat
    }

HInv₀ : HT₀.Invariance BB₀
HInv₀ =
  record
    { Inv_H     = λ c → c
    ; infl      = λ c → ⊑ᵇ-refl {b = c}
    ; idemp-lax = λ c → ⊑ᵇ-refl {b = c}
    }

module ST₀ = Truth.StrictTruth Sig₀

Strict₀ : ST₀.StrictLayer Bool
Strict₀ = record { Sat_S = λ _ φ → SatBool φ }

coh-LH₀
  : ∀ (w : LogOSSignature.Cosp Sig₀) (φ : Bool)
  → (ST₀.StrictLayer.Sat_S Strict₀ w φ) ↔ (HT₀.HLayer.Sat_H HTruth₀ w φ)
coh-LH₀ _ _ = intro (λ x → x) (λ x → x)

Sat_H_bnd₀ : LogOSSignature.∂Cosp Sig₀ → Bool → Set lzero
Sat_H_bnd₀ _ c = SatBool c

sat-coh₀
  : ∀ (w : LogOSSignature.Cosp Sig₀) (c : Bool)
  → HT₀.HLayer.Sat_H HTruth₀ w c ↔ Sat_H_bnd₀ (LogOSSignature.to∂ Sig₀ w) c
sat-coh₀ _ _ = intro (λ x → x) (λ x → x)

-- --------------------------------------------------------------------------
-- Kernel shape + logic kernel
-- --------------------------------------------------------------------------

Shape₀ : Core.KernelShape Sig₀ QNatMul
Shape₀ =
  record
    { HWorld = W₀
    ; BB     = BB₀
    ; MBulk  = Mᵇ
    ; MBnd   = Mᵇ
    ; Holo   = Holo₀
    ; HTruth = HTruth₀
    ; HInv   = HInv₀
    ; Sat_H_bnd = Sat_H_bnd₀
    ; sat-coh   = sat-coh₀
    ; Fml    = Bool
    ; Strict = Strict₀
    ; TransH = λ φ → φ
    ; coh-LH = λ w φ → coh-LH₀ w φ
    ; Code   = Bool
    ; encode = λ c → c
    ; decode = λ γ → γ
    ; Guard  = λ γ → γ
    ; Body   = λ γ → γ
    ; γ*     = true
    ; reify  = λ γ → γ
    ; Body∂  = λ c → c
    }

ShapeLaws₀ : Core.KernelShapeLaws Shape₀
ShapeLaws₀ =
  record
    { decode∘encode = λ _ → refl
    ; γ*-guard =
        (tt , tt)
    ; reify-decode = λ _ → refl
    ; body-decode  = λ _ → refl
    }

GTier₀ : LK.GTier QNatMul (BulkBoundary.bnd BB₀)
GTier₀ =
  record
    { Step = ⊤
    ; step = tt
    ; sat  = tt
    ; Flow = λ _ c → c
    ; mono = λ le → le
    ; infl-sat  = λ c → ⊑ᵇ-refl {b = c}
    ; idemp-sat = λ c → ⊑ᵇ-refl {b = c}
    ; Th* = true
    ; Th*-fixed =
        (tt , tt)
    }

LogicKernel₀ : LK.LogicKernel Sig₀ QNatMul
LogicKernel₀ =
  record
    { shape      = Shape₀
    ; shapeLaws  = ShapeLaws₀
    ; G          = GTier₀
    ; guard-decode = λ _ → refl
    ; decode-γ*    = refl
    }

-- --------------------------------------------------------------------------
-- Vacuity-guard witnesses
-- --------------------------------------------------------------------------

true≢false : ¬ (true ≡ false)
true≢false ()

suc0≢0 : ¬ (suc zero ≡ zero)
suc0≢0 ()

qGuards₀ : QGuards.QAdapterVacuityGuards QNatMul
qGuards₀ =
  record
    { a              = suc zero
    ; a-not-bottom   = suc0≢0
    ; unit-not-bottom = suc0≢0
    }

kernelGuards₀ : LKVac.KernelVacuityGuards LogicKernel₀
kernelGuards₀ =
  record
    { c₀    = true
    ; c₁    = false
    ; w     = tt
    ; sat₀  = tt
    ; unsat₁ = λ ()
    }

B₀ : BoundaryIO Sig₀ QNatMul (LK.LogicKernel.HWorld LogicKernel₀) (LK.LogicKernel.BB LogicKernel₀) (LK.LogicKernel.HTruth LogicKernel₀)
B₀ = LKBoundary.boundaryIO LogicKernel₀

Sem₀ : BoundarySemantics Sig₀ QNatMul (LK.LogicKernel.HWorld LogicKernel₀) (LK.LogicKernel.BB LogicKernel₀) (LK.LogicKernel.HTruth LogicKernel₀) B₀
Sem₀ =
  record
    { Form    = Bool
    ; SatF    = BoundaryIO.Sat∂ B₀
    ; Interp  = λ c → c
    ; Sat∂≈F  = λ _ _ → intro (λ x → x) (λ x → x)
    }

Port₀ : BoundaryPort Sig₀ QNatMul (LK.LogicKernel.HWorld LogicKernel₀) (LK.LogicKernel.BB LogicKernel₀) (LK.LogicKernel.HTruth LogicKernel₀) B₀
Port₀ =
  record
    { Sem     = Sem₀
    ; Import  = λ φ → φ
    ; SatF≈∂  = λ _ _ → intro (λ x → x) (λ x → x)
    }

portGuards₀ : PortVac.PortVacuityGuards B₀ Port₀
portGuards₀ =
  record
    { p = tt
    ; φ₀ = true
    ; φ₁ = false
    ; sat₀ = tt
    ; unsat₁ = λ ()
    }

idAdapter₀ : PortAdapter B₀ Port₀ Port₀
idAdapter₀ =
  record
    { map = λ φ → φ
    ; preserves-Sat = λ _ _ → intro (λ x → x) (λ x → x)
    }

adapterGuards₀ : PortVac.AdapterVacuityGuards B₀ Port₀ Port₀ idAdapter₀
adapterGuards₀ =
  record
    { p = tt
    ; φ₀ = true
    ; φ₁ = false
    ; sat₀ = tt
    ; unsat₁ = λ ()
    ; map-distinct = true≢false
    }
