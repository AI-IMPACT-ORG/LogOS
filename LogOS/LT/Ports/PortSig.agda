{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.PortSig where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Port signature vocabulary:
-- a port is a displayed thin 2-category over some base category `C`, tagged by
-- a small first-order label `label` together with a type-level payload `Tag`.
--
-- Design pattern:
-- when LogOS needs raw lookup/no-dup/shadowing, it separates first-order
-- identity from dependent semantics. The label carries the former; the payload
-- and displayed structure carry the latter.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)

-- First-order identity carrier for raw stack operations.
PortLabel : Set
PortLabel = ℕ

-- A port signature: a displayed structure over `C`, tagged by `Tag`.
--
-- Universe note:
-- the displayed object/hom levels are part of the *data*, so this record lives
-- in `Setω` to avoid fixing an a-priori bound.
-- Design note:
-- the first-order label `label` is what raw stack membership/no-dup compares.
-- The richer `Tag` payload remains available for module-local typing, but is
-- intentionally not used as the raw membership index under `--without-K`.
record PortSig
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (label : PortLabel)
  {ℓTag : Level}
  (Tag : Set ℓTag)
  : Setω where
  field
    ℓDObj ℓDHom : Level
    Displayed : DisplayedThin2Cat C ℓDObj ℓDHom

open PortSig public using (Displayed)

-- A port entry: the full dependent payload named by a first-order label.
--
-- Raw membership/no-dup compare only `label`. Typed access and forgetting use
-- the whole entry.
record PortEntry
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Setω where
  constructor mkPortEntry
  field
    label : PortLabel
    ℓTag : Level
    Tag : Set ℓTag
    sig : PortSig C label Tag

open PortEntry public using (sig) renaming (Tag to TagTy; ℓTag to Tagℓ; label to LabelOf)

-- Build an entry from its signature (avoids repeating the tag arguments).
mkEntry
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {label : PortLabel}
    {ℓTag : Level} {Tag : Set ℓTag}
  → PortSig C label Tag
  → PortEntry C
mkEntry {label = label} {ℓTag = ℓTag} {Tag = Tag} sig =
  mkPortEntry label ℓTag Tag sig
