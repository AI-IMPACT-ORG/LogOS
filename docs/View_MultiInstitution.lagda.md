<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS — Classic (Model-Theoretic) Presentation as a Multi-Institution

```agda
module docs.View_MultiInstitution where

open import LogOS.Docs.Views.View_MultiInstitution public
```

This note is a documentation artefact written in a paper-ready style. It gives a
classic model-theoretic view of the LogOS kernel architecture as a **multi-institution**.

It is intentionally “implementation-aligned”: where the Agda library does not
currently expose a notion (e.g. a category of signature morphisms), we make the
weakest choice consistent with the code (e.g. take signatures as a discrete category).

## Institutions (recall)

We recall the standard definition of an *institution* (Goguen–Burstall) as an abstract
model theory.

**Definition (Institution).** An institution $\mathcal{I}$ is a tuple
$$
  \mathcal{I} = (\mathbf{Sig}, \mathrm{Sen}, \mathrm{Mod}, \models)
$$
consisting of:

- a category $\mathbf{Sig}$ of signatures,
- a functor $\mathrm{Sen} : \mathbf{Sig} \to \mathbf{Set}$ assigning to each signature $\Sigma$
  a set $\mathrm{Sen}(\Sigma)$ of sentences,
- a functor $\mathrm{Mod} : \mathbf{Sig}^{op} \to \mathbf{Cat}$ assigning to each signature $\Sigma$
  a category $\mathrm{Mod}(\Sigma)$ of models,
- for each signature $\Sigma$, a satisfaction relation
  $$
    \models_\Sigma \;\subseteq\; |\mathrm{Mod}(\Sigma)| \times \mathrm{Sen}(\Sigma)
  $$
  between the objects of $\mathrm{Mod}(\Sigma)$ and sentences $\mathrm{Sen}(\Sigma)$,

subject to the **satisfaction condition**: for every signature morphism
$\sigma : \Sigma \to \Sigma'$, every model $M' \in |\mathrm{Mod}(\Sigma')|$, and every sentence
$\varphi \in \mathrm{Sen}(\Sigma)$,
$$
  M' \models_{\Sigma'} \mathrm{Sen}(\sigma)(\varphi)
  \quad\Longleftrightarrow\quad
  \mathrm{Mod}(\sigma)(M') \models_{\Sigma} \varphi.
$$

**Remark (signatures in LogOS).** The Agda implementation is parameterized by a signature
(a record of primitive carriers/operations). The library does provide *structure-preserving*
signature maps (`LogOS.Base.Signature.Hom.SigHom`) together with identity and composition,
enough to view signatures as a small category if desired.

For a presentation that stays maximally close to the current documentation surfaces (and
avoids committing to any particular choice of `Sen`/`Mod` reindexing functoriality in this
note), one may also take $\mathbf{Sig}$ to be a **discrete category** of signatures. Then
the satisfaction condition is tautological. Nothing below relies on nontrivial signature
morphisms.

## LogOS kernels as an indexed family of institutions

Fix a LogOS **Kernel** $K$ (in the sense of the Agda record `LogOS.Kernel`). It packages:

- three tiers of truth (S/H/G),
- a boundary constraint language (a preorder),
- and a reflective code interface.

We use the following correspondence to the Agda fields:

- $\mathrm{World} := \texttt{Cosp}$ (worlds/contexts),
- $\mathrm{Con}_\partial :=$ boundary constraints (a preorder),
- $\mathrm{Fml} :=$ strict-layer formulas,
- $\mathrm{Sat}_S(w,\varphi)$ and $\mathrm{Sat}_H(w,c)$ are the S- and H-layer satisfactions,
- $\mathrm{Flow} : \mathrm{Con}_\partial \to \mathrm{Con}_\partial$ is a closure/nucleus
  (this is the `Flow` field of `GuardedTruth.GuardedClosure` in the Kernel/Minimal code),
- $\mathrm{Th}^\ast$ is a distinguished (preorder) fixed point witness (global stable truth),
- $\mathrm{Trans}_H : \mathrm{Fml} \to \mathrm{Con}_\partial$ is the S→H translation.

The kernel coherence laws include:
$$
  \mathrm{Sat}_S(w,\varphi) \iff \mathrm{Sat}_H\!\bigl(w,\mathrm{Trans}_H(\varphi)\bigr)
$$
and the reflective coherence law:
$$
  \mathrm{decode}(\mathrm{Guard}(\gamma)) \;\equiv\; \mathrm{Flow}(\mathrm{decode}(\gamma)).
$$
where $\equiv$ should be read as the library’s propositional equality (Agda’s `_≡_`),
not a definitional equality.

### S-institution: strict formulas

Define an institution $\mathcal{I}_S(K)$ (“S-tier”) by:

- $\mathbf{Sig}$: discrete category with the chosen kernel signature as an object,
- $\mathrm{Sen}_S(\Sigma) := \mathrm{Fml}$,
- $\mathrm{Mod}_S(\Sigma) :=$ the discrete category on the set $\mathrm{World}$,
- satisfaction: $w \models_S \varphi$ iff $\mathrm{Sat}_S(w,\varphi)$.

**Remark.** One can strengthen $\mathrm{Mod}_S$ and $\mathrm{Mod}_H$ to preorder categories using the kernel’s
world order (`WorldH._≤ctx_`) and rely on monotonicity of satisfaction. This note keeps models discrete to
stay maximally conservative.

### H-institution: boundary constraints

Define an institution $\mathcal{I}_H(K)$ (“H-tier”) by:

- $\mathrm{Sen}_H(\Sigma) := \mathrm{Con}_\partial$,
- $\mathrm{Mod}_H(\Sigma) :=$ the discrete category on $\mathrm{World}$,
- satisfaction: $w \models_H c$ iff $\mathrm{Sat}_H(w,c)$.

### G-institution: stable theories (Flow fixed points)

The guarded tier is most naturally a **consequence/closure** interface. A standard
model-theoretic presentation uses **fixed points** of the closure operator as models.

Let $\mathrm{Fix}(\mathrm{Flow})$ be the set of constraints $t \in \mathrm{Con}_\partial$
that are fixed by the closure (up to preorder equivalence), i.e. $t \preceq \mathrm{Flow}(t)$
and $\mathrm{Flow}(t) \preceq t$.

Define an institution $\mathcal{I}_G(K)$ (“G-tier”) by:

- $\mathrm{Sen}_G(\Sigma) := \mathrm{Con}_\partial$,
- $\mathrm{Mod}_G(\Sigma) :=$ the preorder-category of fixed points $\mathrm{Fix}(\mathrm{Flow})$,
- satisfaction: $t \models_G c$ iff $t \preceq c$ in the boundary preorder.

In this view, $\mathrm{Th}^\ast$ is a distinguished model representing “global stable truth”.
Under additional order/continuity structure (not assumed in the minimal kernel interface),
one can upgrade this to a genuine “least fixed point / least model” presentation.

## Multi-institution structure (S/H/G together)

LogOS does not provide only one institution; it provides **three** interlocked tiers.
We therefore present it as a **multi-institution**.

**Definition (Multi-institution, schematic).** A multi-institution consists of:

- a small index category $\mathbf{L}$ of *levels*,
- for each $\ell \in \mathbf{L}$ an institution $\mathcal{I}_\ell$ (over a shared $\mathbf{Sig}$),
- for selected arrows $\ell \to \ell'$ in $\mathbf{L}$, sentence translations
  $\tau_{\ell\to\ell'} : \mathrm{Sen}_\ell(\Sigma) \to \mathrm{Sen}_{\ell'}(\Sigma)$
  that preserve satisfaction in the appropriate direction.

For LogOS, take $\mathbf{L}$ to be the walking diagram
$$
  S \xrightarrow{\;\tau_{S\to H}\;} H \xrightarrow{\;\tau_{H\to G}\;} G
$$
and define:

- $\mathcal{I}_S(K), \mathcal{I}_H(K), \mathcal{I}_G(K)$ as above,
- $\tau_{S\to H} := \mathrm{Trans}_H$ (kernel field),
- the kernel coherence law gives, for each world $w$:
  $$
    w \models_S \varphi \iff w \models_H \tau_{S\to H}(\varphi).
  $$

The map $H \to G$ is not primarily a sentence translation; it is a change of **model class**:
G-models are the $\mathrm{Flow}$-stable constraints, and satisfaction is the underlying
preorder entailment. This is a standard way to express “truth as closure/fixed point” in a
classical model-theoretic idiom.

## Reflection (Kernel I/O) as internal syntax for G

Beyond the model-theoretic picture, LogOS kernels expose a reflective **code language**:
$$
  \mathrm{encode} : \mathrm{Con}_\partial \to \mathrm{Code},
  \qquad
  \mathrm{decode} : \mathrm{Code} \to \mathrm{Con}_\partial,
  \qquad
  \mathrm{Guard} : \mathrm{Code} \to \mathrm{Code},
$$
with $\mathrm{decode}\circ \mathrm{encode} = \mathrm{id}$ and the key coherence law:
$$
  \mathrm{decode}(\mathrm{encode}(c)) \;\equiv\; c,
  \qquad
  \mathrm{decode}(\mathrm{Guard}(\gamma)) \;\equiv\; \mathrm{Flow}(\mathrm{decode}(\gamma)).
$$

This can be read as: the G-tier closure operator is **internalized** by a single admissible
code step. This is exactly the interface used by the diagonal/Rice/Tarski-style meta theorems,
while keeping all assumptions explicit.

## Reference

- J. A. Goguen and R. M. Burstall, *Institutions: Abstract model theory for specification and programming*, Journal of the ACM, 39(1):95–146, 1992.
