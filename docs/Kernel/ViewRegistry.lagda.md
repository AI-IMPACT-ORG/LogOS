<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Canonical View Registry (Relation Ontology)

```agda
{-# OPTIONS --safe #-}
module docs.Kernel.ViewRegistry where

open import LogOS.Prelude

open import LogOS.Minimal.View
open import LogOS.Minimal.RelPreorder using (EqRelPreorder)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel
open import LogOS.Kernel.Graded using (GradedKernel)
open import LogOS.Kernel.Tiers
open import LogOS.Kernel.Eq using (module ForKernel; module ForKernelLike; module ForGradedKernel)
```

This page is a **registry of canonical views** (in the sense of `LogOS.Minimal.View`)
used to induce domain relations by pullback.

Rule (one line)
---------------
Every domain-specific preorder/equality on a type `X` must be introduced as a pullback
along an explicit named view `V : View X T` into a named target preorder `T`.

Registry: Kernel tiers
----------------------
For any kernel `K`, `LogOS/Kernel/Tiers.agda` provides the canonical semantic targets and views:

```agda
module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : Kernel Sig Q) where
  module T = LogOS.Kernel.Tiers.For K
  open T

  -- Order-theoretic H-target preorder and the canonical views into it.
  _ : View (Kernel.Code K) RPᴴ
  _ = decodeView

  _ : View (Kernel.Fml K) RPᴴ
  _ = transHView

  -- Satisfaction-induced observational target (boundary observations) + view.
  _ : View (Kernel.Code K) CPᴴᵒ
  _ = decodeObsView
```

Registry: Strict decode equality (shape-only / graded)
------------------------------------------------------
When you only need strict “same decoded meaning” on code (pullback of `≡` along `decode`),
use the dedicated aliases:

```agda
module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : Kernel Sig Q) where
  open ForKernel K
  -- `_≃K_` is strict pullback equality: `decode γ₁ ≡ decode γ₂`.
  _ : Kernel.Code K → Kernel.Code K → Set ℓ
  _ = _≃K_

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : KernelLike Sig Q) where
  open ForKernelLike K
  _ : KernelLike.Code K → KernelLike.Code K → Set ℓ
  _ = _≃K_

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : GradedKernel Sig Q) where
  open ForGradedKernel K
  _ : GradedKernel.Code K → GradedKernel.Code K → Set ℓ
  _ = _≃K_
```

Registry: Equality as a target preorder
---------------------------------------
For strict views into a plain semantic type `M`, use the equality preorder target:

- `EqRelPreorder M : RelPreorder ℓ ℓ` with relation `_≡_`.

Then `x ≃[V] y` is definitionally `μ x ≡ μ y`.

How to add a new domain equality
--------------------------------
To introduce a new equality/preorder on a domain `X`:

1. choose a semantic target preorder `T` (often `ObsPreorder Sat`),
2. export a named view `V : View X T`,
3. export only pullbacks `_⊑[ V ]_`, `_≈[ V ]_`, `_≃[ V ]_` (and optionally view-named aliases),
4. in prose, cite the view (e.g. “`≈run` induced by `run : X → M`”).

Avoid defining primitive “≈” operators that are secretly `≡` (use `≃` instead).
