{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Concurrency.HappensBefore where

-- Shared-boundary / many-realisations specialization for concurrency.
--
-- - constraints are happens-before relations between events,
-- - refinement is implication (more edges = stronger constraint),
-- - `Flow` is transitive closure (effective/causal completion),
-- - “race-freedom” is phrased as *effective* ordering of a conflict pair.
--
-- This module is intentionally the smallest uniform specialization of the
-- shared-boundary / many-realisations discipline:
-- the interesting content lives in (1) the chosen boundary preorder,
-- (2) the chosen closure, and (3) the race-freedom predicate.
-- The transport theorem below is inherited architecture, not bespoke plumbing.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
open import LogOS.LT.Flow using (GuardedClosure; Flow; Stable; mkStable)
open import LogOS.LT.Kernel using (Kernel; bnd; decode)
open import LogOS.LT.Hom using (KernelHom)
open import LogOS.LT.HomFlow using (KernelHomFlow)
import LogOS.LT.Hom as Hom
import LogOS.LT.Theorems.Effectivisation as Eff
open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)

-- --------------------------------------------------------------------------
-- Boundary: happens-before relations ordered by implication.

data Event : Set where
  w1 barrier w2 : Event

HB : Set₁
HB = Event → Event → Set

infix 4 _⊑HB_
_⊑HB_ : HB → HB → Set
R ⊑HB S = ∀ x y → R x y → S x y

HBPreorder : ConPreorder (lsuc lzero) lzero
HBPreorder =
  record
    { Con = HB
    ; _⊑_ = _⊑HB_
    ; refl = λ _ _ r → r
    ; trans = λ rs st x y r → st x y (rs x y r)
    }

-- --------------------------------------------------------------------------
-- Causal closure: transitive closure (paths).

data Reach (R : HB) : Event → Event → Set where
  step  : ∀ {x y} → R x y → Reach R x y
  chain : ∀ {x y z} → Reach R x y → Reach R y z → Reach R x z

reach-mono : ∀ {R S} → R ⊑HB S → (Reach R ⊑HB Reach S)
reach-mono rs x y (step r) = step (rs x y r)
reach-mono rs x z (chain p q) = chain (reach-mono rs x _ p) (reach-mono rs _ z q)

reach-infl : ∀ R → R ⊑HB Reach R
reach-infl _ _ _ r = step r

reach-flatten : ∀ {R} → Reach (Reach R) ⊑HB Reach R
reach-flatten _ _ (step p) = p
reach-flatten x z (chain p q) = chain (reach-flatten x _ p) (reach-flatten _ z q)

HBClosure : GuardedClosure HBPreorder
HBClosure =
  record
    { Flow = Reach
    ; mono = reach-mono
    ; infl = reach-infl
    ; idemp-lax = λ _ → reach-flatten
    }

HBPhysicalSemantics : DependentLocalSemantics {lzero} {lsuc lzero} {lzero}
HBPhysicalSemantics =
  record
    { I = ⊤
    ; O = λ _ → HBPreorder
    ; GC₀ = λ _ → HBClosure
    }

-- --------------------------------------------------------------------------
-- A minimal “race-free” predicate (conflict pair: w1 vs w2).

-- `RaceFree R` means the *effective* happens-before closure orders the designated
-- conflict pair (`w1`,`w2`).
--
-- This is intentionally minimal: it does not attempt to model a full memory
-- model, nor “race freedom” for arbitrary read/write sets.
RaceFree : HB → Set
RaceFree R = Flow HBClosure R w1 w2 ⊎ Flow HBClosure R w2 w1

raceFree-mono : ∀ {R S} → R ⊑HB S → RaceFree R → RaceFree S
raceFree-mono rs (inj₁ p) = inj₁ (GuardedClosure.mono HBClosure rs w1 w2 p)
raceFree-mono rs (inj₂ p) = inj₂ (GuardedClosure.mono HBClosure rs w2 w1 p)

-- Same monotonicity, but phrased directly in terms of the effective semantics
-- (`Flow`-closed view) that `RaceFree` depends on.
raceFree-flow-mono
  : ∀ {R S} → Flow HBClosure R ⊑HB Flow HBClosure S → RaceFree R → RaceFree S
raceFree-flow-mono rs (inj₁ p) = inj₁ (rs w1 w2 p)
raceFree-flow-mono rs (inj₂ p) = inj₂ (rs w2 w1 p)

-- --------------------------------------------------------------------------
-- A minimal kernel: “programs” decode to micro happens-before constraints.

data Program : Set where
  safe racy : Program

microHB : Program → HB
microHB safe w1 w1 = ⊥
microHB safe w1 barrier = ⊤
microHB safe w1 w2 = ⊥
microHB safe barrier w1 = ⊥
microHB safe barrier barrier = ⊥
microHB safe barrier w2 = ⊤
microHB safe w2 w1 = ⊥
microHB safe w2 barrier = ⊥
microHB safe w2 w2 = ⊥
microHB racy _ _ = ⊥

ProgramKernel : Kernel (lsuc lzero) lzero lzero
ProgramKernel =
  record
    { bnd = HBPreorder
    ; Code = Program
    ; decode = microHB
    }

-- Effective semantics: close the micro constraints under causality.
EffectiveKernel : Kernel (lsuc lzero) lzero lzero
EffectiveKernel = Eff.effectiveKernel ProgramKernel HBClosure

-- “Effective outputs are stable” (they are already closed under `Flow`).
effective-stable : ∀ p → Stable {CP = HBPreorder} (Flow HBClosure)
effective-stable p =
  mkStable
    (decode EffectiveKernel p)
    (GuardedClosure.idemp-lax HBClosure (decode ProgramKernel p))

-- Concrete: the barrier induces w1 ≺ w2 in the effective closure.
safe-raceFree : RaceFree (decode ProgramKernel safe)
safe-raceFree = inj₁ (chain {x = w1} {y = barrier} {z = w2} (step tt) (step tt))

-- Concrete: an empty happens-before graph cannot prove race-freedom.
noReach-empty : ∀ {x y} → Reach (microHB racy) x y → ⊥ {lzero}
noReach-empty (step ())
noReach-empty (chain p q) = noReach-empty p

not-raceFree-racy : ¬ RaceFree (decode ProgramKernel racy)
not-raceFree-racy (inj₁ p) = noReach-empty p
not-raceFree-racy (inj₂ p) = noReach-empty p

-- --------------------------------------------------------------------------
-- Tooling loop (debugger story):
--
-- If you only expose *effective* semantics (`Flow ∘ decode`) and your adapters
-- preserve `Flow`, then race-freedom is preserved automatically.

record HBKernel (ℓCode : Level) : Set (lsuc (lsuc lzero ⊔ ℓCode)) where
  field
    Code  : Set ℓCode
    decodeHB : Code → HB

  K : Kernel (lsuc lzero) lzero ℓCode
  K =
    record
      { bnd = HBPreorder
      ; Code = Code
      ; decode = decodeHB
      }

open HBKernel public

-- --------------------------------------------------------------------------
-- App-specific content:
-- the chosen boundary preorder, closure, and race-freedom predicate.
--
-- Inherited architecture:
-- transport of race-freedom along shared-boundary translations.
raceFree-transport
  : ∀ {ℓCode : Level}
    {A B : HBKernel ℓCode}
    (h : KernelHom (K A) (K B))
  -- Shared-boundary lift: source observations remain valid after translation.
  → (∀ c → _⊑_ HBPreorder c (Hom.map∂ h c))
  → KernelHomFlow HBClosure HBClosure h
  → ∀ γ
  → RaceFree (decodeHB A γ)
  → RaceFree (decodeHB B (Hom.mapCode h γ))
raceFree-transport {A = A} {B = B} h shared hf γ rf =
  raceFree-flow-mono comm' rf
  where
    -- Normalisation commutes with translation up to refinement (kernel-level theorem).
    comm :
      _⊑_ HBPreorder
        (Hom.map∂ h (Flow HBClosure (decodeHB A γ)))
        (Flow HBClosure (decodeHB B (Hom.mapCode h γ)))
    comm = Eff.normalize-decode-mapCode HBClosure HBClosure h hf γ

    comm' :
      _⊑_ HBPreorder
        (Flow HBClosure (decodeHB A γ))
        (Flow HBClosure (decodeHB B (Hom.mapCode h γ)))
    comm' =
      let
        module R = LogOS.Prelude.RefinementKit.Reasoning HBPreorder
        open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
      in
      begin⊑
        Flow HBClosure (decodeHB A γ)
          ⊑⟨ shared (Flow HBClosure (decodeHB A γ)) ⟩
        Hom.map∂ h (Flow HBClosure (decodeHB A γ))
          ⊑⟨ comm ⟩
        Flow HBClosure (decodeHB B (Hom.mapCode h γ))
          ∎⊑

sharedBoundaryTransport = raceFree-transport
