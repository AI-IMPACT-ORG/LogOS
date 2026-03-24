<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Example: Deutsch-style category construction for Wolfram Rule 110 (as a semiconjugacy-style quotient)

This file formalises a standard construction underlying the statement:

> Rule 110 is a quotient of a Deutsch system.

Here “quotient” is meant in the dynamical-systems sense: we exhibit an
observation map and prove a semiconjugacy (commuting) law; we do not assert
surjectivity.

Construction principle (standard in dynamics / symbolic dynamics):

- the **Deutsch refinement** is the time shift on **bi-infinite space–time histories**
  satisfying the local Rule 110 constraint; in LogOS/v1.1 the reversible structure
  is expressed via *local* order-isomorphisms on per-cell observable timelines
  (the local-reversibility port);
- the **observation map** is the time-0 slice (discard the rest of the history);
- the usual Rule 110 step is recovered from the validity constraint, yielding the
  semiconjugacy law.

Although the motivating statement is about Rule 110, the construction below is
uniform:

- the “history shift + time-0 slice” quotient law is defined for *any* radius-1
  local rule `Bit → Bit → Bit → Bit` (an elementary cellular automaton); and
- the specific Wolfram rules arise by the standard bit-extraction encoding
  `wolframRule n`, for any `n : ℕ`.

Agda note: module name parts cannot contain a *pure numeral* segment. Since Agda
parses underscores as mixfix separators, `...Rule_110` would contain the segment
`110` and is rejected; hence the identifier `Rule110`.

We keep the example host-minimal and use only the curated API surface:

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Examples.Example_AbstractDeutsch_Category_Wolfram_Rule110 where

open import LogOS.API.LT
open import LogOS.API.Ports.PhysicalOptional.Deutsch using (module DeutschSlice)
open ImplementationView using (_⇒_)
open SuccessorIndex using (Stageω; zero; suc)

ℕ : Set
ℕ = Stageω

-- --------------------------------------------------------------------------
-- A minimal Bit type and Wolfram rule 110.
--
-- We define it *literally* from Wolfram numbering: the output bit is the
-- neighbourhood-indexed bit of the natural number `110`.
--
-- The familiar 8-clause transition table is then *derived by definitional reduction*.

data Bit : Set where
  off on : Bit

-- Wolfram numbering as bit-extraction on ℕ.
--
-- Neighbourhood value (binary):
--   off/off/off ↦ 0  ...  on/on/on ↦ 7
-- i.e. index = 4·l + 2·c + r for bits l,c,r ∈ {0,1}.

bitVal : Bit → ℕ
bitVal off = zero
bitVal on  = suc zero

infixl 6 _+ℕ_
_+ℕ_ : ℕ → ℕ → ℕ
zero  +ℕ n = n
suc m +ℕ n = suc (m +ℕ n)

doubleℕ : ℕ → ℕ
doubleℕ n = n +ℕ n

neighVal : Bit → Bit → Bit → ℕ
neighVal l c r = bitVal r +ℕ doubleℕ (bitVal c +ℕ doubleℕ (bitVal l))

-- Integer division by 2 (floor), defined by structural recursion.
half : ℕ → ℕ
half zero          = zero
half (suc zero)    = zero
half (suc (suc n)) = suc (half n)

-- Parity bit: least significant bit of a natural number.
parityBit : ℕ → Bit
parityBit zero          = off
parityBit (suc zero)    = on
parityBit (suc (suc n)) = parityBit n

-- `bitAt n k` is the k-th binary digit of n (LSB = k=0), as a `Bit`.
bitAt : ℕ → ℕ → Bit
bitAt n zero    = parityBit n
bitAt n (suc k) = bitAt (half n) k

wolframRule : ℕ → Bit → Bit → Bit → Bit
wolframRule n l c r = bitAt n (neighVal l c r)

n110 : ℕ
n110 =
  bitVal off +ℕ doubleℕ
    ( bitVal on +ℕ doubleℕ
        ( bitVal on +ℕ doubleℕ
            ( bitVal on +ℕ doubleℕ
                ( bitVal off +ℕ doubleℕ
                    ( bitVal on +ℕ doubleℕ
                        ( bitVal on +ℕ doubleℕ
                            ( bitVal off ) ) ) ) ) ) )

rule110 : Bit → Bit → Bit → Bit
rule110 = wolframRule n110

-- Derived transition table (Wolfram order 111,110,101,100,011,010,001,000):
--
--   111↦0, 110↦1, 101↦1, 100↦0, 011↦1, 010↦1, 001↦1, 000↦0
--
-- Each clause is definitionally `refl`, i.e. the table is obtained by reducing
-- `rule110 = wolframRule 110`.

rule110-111 : rule110 on  on  on  ≡ off
rule110-111 = refl

rule110-110 : rule110 on  on  off ≡ on
rule110-110 = refl

rule110-101 : rule110 on  off on  ≡ on
rule110-101 = refl

rule110-100 : rule110 on  off off ≡ off
rule110-100 = refl

rule110-011 : rule110 off on  on  ≡ on
rule110-011 = refl

rule110-010 : rule110 off on  off ≡ on
rule110-010 = refl

rule110-001 : rule110 off off on  ≡ on
rule110-001 = refl

rule110-000 : rule110 off off off ≡ off
rule110-000 = refl

-- Sanity check: another rule number is handled the same way.
-- (If you intended “the 101 clause of Rule 110”, that is `rule110-101` above.)

n101 : ℕ
n101 =
  bitVal on +ℕ doubleℕ
    ( bitVal off +ℕ doubleℕ
        ( bitVal on +ℕ doubleℕ
            ( bitVal off +ℕ doubleℕ
                ( bitVal off +ℕ doubleℕ
                    ( bitVal on +ℕ doubleℕ
                        ( bitVal on +ℕ doubleℕ
                            ( bitVal off ) ) ) ) ) ) )

rule101 : Bit → Bit → Bit → Bit
rule101 = wolframRule n101

-- Wolfram order 111,110,101,100,011,010,001,000:
--
--   111↦0, 110↦1, 101↦1, 100↦0, 011↦0, 010↦1, 001↦0, 000↦1

rule101-111 : rule101 on  on  on  ≡ off
rule101-111 = refl

rule101-110 : rule101 on  on  off ≡ on
rule101-110 = refl

rule101-101 : rule101 on  off on  ≡ on
rule101-101 = refl

rule101-100 : rule101 on  off off ≡ off
rule101-100 = refl

rule101-011 : rule101 off on  on  ≡ off
rule101-011 = refl

rule101-010 : rule101 off on  off ≡ on
rule101-010 = refl

rule101-001 : rule101 off off on  ≡ off
rule101-001 = refl

rule101-000 : rule101 off off off ≡ on
rule101-000 = refl

-- --------------------------------------------------------------------------
-- Encode the transition table back into the Wolfram rule number.
--
-- This makes the “derived table” correspondence literal: from the eight output
-- bits (in Wolfram order) we reconstruct the natural number whose binary digits
-- are exactly that table.

-- Binary numeral from 8 bits (LSB first).
fromBits8 : Bit → Bit → Bit → Bit → Bit → Bit → Bit → Bit → ℕ
fromBits8 b0 b1 b2 b3 b4 b5 b6 b7 =
  bitVal b0 +ℕ doubleℕ
    ( bitVal b1 +ℕ doubleℕ
        ( bitVal b2 +ℕ doubleℕ
            ( bitVal b3 +ℕ doubleℕ
                ( bitVal b4 +ℕ doubleℕ
                    ( bitVal b5 +ℕ doubleℕ
                        ( bitVal b6 +ℕ doubleℕ
                            ( bitVal b7 ) ) ) ) ) ) )

-- Wolfram order (111,110,101,100,011,010,001,000) with 111 as the MSB.
fromWolframTable : Bit → Bit → Bit → Bit → Bit → Bit → Bit → Bit → ℕ
fromWolframTable b111 b110 b101 b100 b011 b010 b001 b000 =
  fromBits8 b000 b001 b010 b011 b100 b101 b110 b111

wolframNumber : (Bit → Bit → Bit → Bit) → ℕ
wolframNumber f =
  fromWolframTable
    (f on  on  on)
    (f on  on  off)
    (f on  off on)
    (f on  off off)
    (f off on  on)
    (f off on  off)
    (f off off on)
    (f off off off)

-- “Rule number modulo 256” (low 8 bits), stated in the same bit-extraction
-- vocabulary used by `wolframRule`.
--
-- We avoid defining a separate division-based `mod` operator here: `low8` is
-- literally the reconstruction of the low 8 bits as a natural number.

one two three four five six seven : ℕ
one = suc zero
two = suc one
three = suc two
four = suc three
five = suc four
six = suc five
seven = suc six

low8 : ℕ → ℕ
low8 n =
  fromBits8
    (bitAt n zero)
    (bitAt n one)
    (bitAt n two)
    (bitAt n three)
    (bitAt n four)
    (bitAt n five)
    (bitAt n six)
    (bitAt n seven)

wolframNumber-wolframRule : ∀ n → wolframNumber (wolframRule n) ≡ low8 n
wolframNumber-wolframRule _ = refl

-- These compute by definitional reduction once the eight clauses are rewritten.
wolframNumber-rule110 : wolframNumber rule110 ≡ n110
wolframNumber-rule110
  rewrite
    rule110-111 | rule110-110 | rule110-101 | rule110-100
  | rule110-011 | rule110-010 | rule110-001 | rule110-000
  = refl

wolframNumber-rule101 : wolframNumber rule101 ≡ n101
wolframNumber-rule101
  rewrite
    rule101-111 | rule101-110 | rule101-101 | rule101-100
  | rule101-011 | rule101-010 | rule101-001 | rule101-000
  = refl

-- --------------------------------------------------------------------------
-- A minimal integer type ℤ (enough for two-sided time and a two-sided tape).
--
-- Representation:
--   pos n  represents  n
--   neg n  represents -(n+1)

data ℤ : Set where
  pos : ℕ → ℤ
  neg : ℕ → ℤ

sucZ : ℤ → ℤ
sucZ (pos n)      = pos (suc n)
sucZ (neg zero)   = pos zero
sucZ (neg (suc n)) = neg n

predZ : ℤ → ℤ
predZ (pos zero)   = neg zero
predZ (pos (suc n)) = pos n
predZ (neg n)      = neg (suc n)

pred-suc : ∀ z → predZ (sucZ z) ≡ z
pred-suc (pos n)       = refl
pred-suc (neg zero)    = refl
pred-suc (neg (suc n)) = refl

suc-pred : ∀ z → sucZ (predZ z) ≡ z
suc-pred (pos zero)    = refl
suc-pred (pos (suc n)) = refl
suc-pred (neg n)       = refl

Time Cell : Set
Time = ℤ
Cell = ℤ

time0 : Time
time0 = pos zero

-- --------------------------------------------------------------------------
-- Space–time diagrams for an elementary cellular automaton (radius-1 local rule).

LocalRule : Set
LocalRule = Bit → Bit → Bit → Bit

Diagram : Set
Diagram = Time → Cell → Bit

-- --------------------------------------------------------------------------
-- Local observable language: a cell’s entire timeline.
-- We use the discrete (equality) preorder on timelines, so local reversibility
-- becomes literal invertibility of the timeline shift.

Timeline : Set
Timeline = Time → Bit

BitPreorder : ConPreorder lzero lzero
BitPreorder =
  record
    { Con   = Bit
    ; _⊑_   = _≡_
    ; refl  = refl
    ; trans = trans
    }

TimelinePreorder : ConPreorder lzero lzero
TimelinePreorder = FunPreorder Time BitPreorder

shiftTimeline : Timeline → Timeline
shiftTimeline τ t = τ (sucZ t)

unshiftTimeline : Timeline → Timeline
unshiftTimeline τ t = τ (predZ t)

shiftTimeline-mono : MonoMap TimelinePreorder TimelinePreorder shiftTimeline
shiftTimeline-mono le t = le (sucZ t)

unshiftTimeline-mono : MonoMap TimelinePreorder TimelinePreorder unshiftTimeline
unshiftTimeline-mono le t = le (predZ t)

shiftTimeline-iso : OrderIso TimelinePreorder
shiftTimeline-iso =
  record
    { f = shiftTimeline
    ; g = unshiftTimeline
    ; f-mono = shiftTimeline-mono
    ; g-mono = unshiftTimeline-mono
    ; fg≈id = λ τ →
        ( (λ t → cong τ (pred-suc t))
        , (λ t → sym (cong τ (pred-suc t)))
        )
    ; gf≈id = λ τ →
        ( (λ t → cong τ (suc-pred t))
        , (λ t → sym (cong τ (suc-pred t)))
        )
    }

-- --------------------------------------------------------------------------
-- The Deutsch refinement (history systems) as a shared distributed-semantics ledger + kernel.
--
-- Locality index: cells.
-- Local observables: a full timeline at each cell.
-- Doctrine: identity closure (so every pointwise boundary map is “causal”).

PS_ECA : DependentLocalSemantics
PS_ECA =
  record
    { I = Cell
    ; O = λ _ → TimelinePreorder
    ; GC₀ = λ _ → idClosure TimelinePreorder
    }

-- --------------------------------------------------------------------------
-- Observable configurations and their boundary kernel.

Config : Set
Config = Cell → Bit

ConfigBoundary : ConPreorder lzero lzero
ConfigBoundary = FunPreorder Cell BitPreorder

configKernel : Kernel lzero lzero lzero
configKernel =
  record
    { bnd = ConfigBoundary
    ; Code = Config
    ; decode = λ c → c
    }

cong₃
  : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {D : Set ℓ₄}
  → (f : A → B → C → D)
    {x x' : A} {y y' : B} {z z' : C}
  → x ≡ x' → y ≡ y' → z ≡ z'
  → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

-- --------------------------------------------------------------------------
-- Generic quotient construction for any local rule.
--
-- Everything below is uniform in the local rule `rule`. The advertised “Rule 110
-- quotient” is obtained by instantiating `rule = rule110`.

module ECA (rule : LocalRule) where

  -- Validity constraint: space–time diagrams satisfy the local update rule.
  Valid : Diagram → Set
  Valid d =
    ∀ t i
    → d (sucZ t) i
      ≡
      rule (d t (predZ i)) (d t i) (d t (sucZ i))

  History : Set
  History = Σ Diagram Valid

  diagramOf : History → Diagram
  diagramOf h = proj₁ h

  validOf : (h : History) → Valid (diagramOf h)
  validOf h = proj₂ h

  -- Time shift on diagrams/histories (invertible at the boundary level).

  shiftDiagram : Diagram → Diagram
  shiftDiagram d t i = d (sucZ t) i

  shiftValid : ∀ {d} → Valid d → Valid (shiftDiagram d)
  shiftValid v t i = v (sucZ t) i

  shiftHistory : History → History
  shiftHistory (d , v) = shiftDiagram d , shiftValid {d = d} v

  open DependentLocalSemantics PS_ECA renaming (Bnd to Bnd_ECA ; GC to GC_ECA)

  module Deutsch = DeutschSlice {ℓCode = lzero} PS_ECA
  module Loc = Deutsch.Locality
  module Cau = Deutsch.Causality
  module Rev = Deutsch.Reversibility
  module D   = Deutsch.Deutsch

  -- The corresponding physical kernel: code is a valid space–time history;
  -- decode returns the per-cell timeline.

  historyKernel : Loc.PhysicalKernel
  historyKernel =
    record
      { Code = History
      ; decode = λ h i t → diagramOf h t i
      }

  -- The physical endomorphism is the time shift:
  -- - boundary action: shift every local timeline,
  -- - code action: shift the whole history.

  shiftPhysical : Loc.PhysicalHom historyKernel historyKernel
  shiftPhysical =
    Loc.mkPhysicalHom
      (λ _ τ t → τ (sucZ t))
      (λ _ → shiftTimeline-mono)
      shiftHistory
      (λ _ → (refl⊑ Bnd_ECA , refl⊑ Bnd_ECA))

  shiftPhysical-causal
    : KernelHomFlow GC_ECA GC_ECA (Loc.physicalToKernelHom shiftPhysical)
  shiftPhysical-causal =
    record { preserves-Flow = λ _ → refl⊑ Bnd_ECA }

  -- Package the history kernel through the causal slice and then into `LOGᴰ`.

  historyCausal : Thin2Cat.Obj Cau.WithPort
  historyCausal =
    mkTotalObjR
      (Loc.physicalObj historyKernel)
      Cau.ttCausal

  historyDeutsch : Thin2Cat.Obj D.WithPort
  historyDeutsch =
    mkTotalObjR
      historyCausal
      Rev.ttReversible

  shiftCausal : Con (Thin2Cat.Hom Cau.WithPort historyCausal historyCausal)
  shiftCausal =
    mkTotalHomR
      shiftPhysical
      shiftPhysical-causal

  shiftPhysical-reversible : Rev.LocalReversible shiftCausal
  shiftPhysical-reversible =
    record
      { isoAt = λ _ → shiftTimeline-iso
      ; forward≈ = λ i x → (refl⊑ (O i) , refl⊑ (O i))
      }

  shiftDeutsch : Con (Thin2Cat.Hom D.WithPort historyDeutsch historyDeutsch)
  shiftDeutsch =
    mkTotalHomR
      shiftCausal
      shiftPhysical-reversible

  -- --------------------------------------------------------------------------
  -- The observation map (time-0 slice) and the induced step function.

  slice0 : History → Config
  slice0 h i = diagramOf h time0 i

  ruleStep : Config → Config
  ruleStep c i = rule (c (predZ i)) (c i) (c (sucZ i))

  -- Semiconjugacy / quotient law (pointwise, avoiding function extensionality):
  -- the time-0 slice after shifting is the one-step update of the time-0 slice.

  quotient-law : ∀ h i → slice0 (shiftHistory h) i ≡ ruleStep (slice0 h) i
  quotient-law h i = validOf h time0 i

  -- --------------------------------------------------------------------------
  -- “Framework-first” restatement:
  -- the quotient law is exactly commutation (up to observational refinement) in LOG.

  historyKernelLT : Kernel lzero lzero lzero
  historyKernelLT = Loc.kernel historyKernel

  shiftKernelLT : KernelHom historyKernelLT historyKernelLT
  shiftKernelLT = Loc.physicalToKernelHom shiftPhysical

  slice0∂ : Con (bnd historyKernelLT) → Con (bnd configKernel)
  slice0∂ F i = F i time0

  slice0Hom : KernelHom historyKernelLT configKernel
  slice0Hom =
    mkKernelHomParts
      (record
        { map∂ = slice0∂
        ; map∂-mono = λ le i → le i time0
        })
      (record
        { mapCode = slice0
        ; decode-mapCode = λ _ → (refl⊑ (bnd configKernel) , refl⊑ (bnd configKernel))
        })

  stepHom : KernelHom configKernel configKernel
  stepHom =
    mkKernelHomParts
      (record
        { map∂ = ruleStep
        ; map∂-mono =
            λ le i →
              cong₃ rule
                (le (predZ i))
                (le i)
                (le (sucZ i))
        })
      (record
        { mapCode = ruleStep
        ; decode-mapCode = λ _ → (refl⊑ (bnd configKernel) , refl⊑ (bnd configKernel))
        })

  stepCommutation
    : (slice0Hom ∘ shiftKernelLT) ⇒ (stepHom ∘ slice0Hom)
  stepCommutation h i = quotient-law h i

-- Any Wolfram rule number yields such a system (and hence a Deutsch quotient).
module WolframECA (n : ℕ) where
  module Sys = ECA (wolframRule n)
  open Sys public

-- Specialise the generic construction to Rule 110 (the example this file is named after).
module Sys110 = ECA rule110

```

Notes (scope and layering):

- `shiftDeutsch` is the Deutsch endomorphism: it lives in `LOGᴰ` for the physical
  semantics `PS_ECA` (local timelines + identity closure).
- `ruleStep` is exhibited only in plain `LOG` (as `stepHom`) inside this
  Deutsch-oriented example: it is not a morphism in the pointwise
  locality-preserving physical category `LOGᵖ`, since it depends on
  neighbouring cells.
- If one wants such a neighbourhood-dependent update as a causal physical
  arrow, the broader causal slice is `LogOS/Ports/AbstractCausal2Cat.agda`;
  this file itself is specifically about the semiconjugacy into the reversible
  Deutsch slice.
- `slice0` is the observation (time-0) map. This file proves only the commuting
  law `quotient-law`; it does *not* claim surjectivity of `slice0` onto all
  configurations.
