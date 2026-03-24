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
-- a type-level payload `Tag`.
--
-- Design pattern:
-- the default port story is capability-first: concrete stack access is carried
-- by exact `PortEntry` witnesses rather than a separate first-order name.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)

-- A port signature: a displayed structure over `C`, tagged by `Tag`.
--
-- Universe note:
-- the displayed object/hom levels are part of the *data*, so this record lives
-- in `Setω` to avoid fixing an a-priori bound.
record PortSig
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  {ℓTag : Level}
  (Tag : Set ℓTag)
  : Setω where
  field
    ℓDObj ℓDHom : Level
    Displayed : DisplayedThin2Cat C ℓDObj ℓDHom

open PortSig public using (Displayed)

-- A port entry: the full dependent payload carried through stacking.
record PortEntry
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Setω where
  constructor mkPortEntry
  field
    ℓTag : Level
    Tag : Set ℓTag
    sig : PortSig C Tag

open PortEntry public using (sig) renaming (Tag to TagTy; ℓTag to Tagℓ)

-- Build an entry from its signature (avoids repeating the tag arguments).
mkEntry
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {ℓTag : Level} {Tag : Set ℓTag}
  → PortSig C Tag
  → PortEntry C
mkEntry {ℓTag = ℓTag} {Tag = Tag} sig =
  mkPortEntry ℓTag Tag sig
