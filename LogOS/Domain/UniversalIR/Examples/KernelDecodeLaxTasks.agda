{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Examples.KernelDecodeLaxTasks where

-- Worked example: a genuine `ProcessHomLax` from kernel functionality.
--
-- The kernel exposes two operational presentations of “one-step computation”:
--
-- - code-level: `Guard ∘ Body` on `Kernel.Code`
-- - boundary-level: `Flow ∘ Body∂` on boundary constraints
--
-- The map `decode : Code → Boundary` is a process morphism; we can view it as a
-- *lax* morphism (`decodeHomLax`) and then use `TransportLax` to obtain a
-- sound over-approximation statement about finite executions.

open import LogOS.Prelude

open import LogOS.Computation.Tasks
import LogOS.Computation.SchemeCategory as Cat
import LogOS.Computation.KernelUniversalProcess as KUP
import LogOS.Domain.UniversalIR.ObservedKernel as ObsKernel

-- Use the minimal, step-homomorphic observation kit (`CodeObsKit`) to obtain a
-- concrete kernel (and therefore a concrete `decodeHomLax`).
module OK = ObsKernel.ForObsKit ObsKernel.CodeObsKit

module KP = KUP.ForKernel OK.ObsKernel

module TCode = ForProcess KP.CodeProcess
module TBnd  = ForProcess KP.BoundaryProcess

-- The boundary step is monotone (for this kernel, it is definitional).
boundaryStepMono : Cat.StepMono KP.BoundaryProcess
boundaryStepMono {c} {d} eq = cong (Cat.Process.Step KP.BoundaryProcess) eq

module TLax = TCode.TransportLax KP.decodeHomLax boundaryStepMono

-- Lax task transport: decoding a finite code execution yields a boundary state
-- that is ≤ the boundary execution of the decoded initial state.
nfTask-decode≤
  : ∀ t
  → Cat.Process._⊑_ KP.BoundaryProcess
      (Cat.ProcessHomLax.map KP.decodeHomLax (TCode.nfTask t))
      (TBnd.nfTask (mapFuelled (Cat.ProcessHomLax.map KP.decodeHomLax) t))
nfTask-decode≤ = TLax.nfTask-map≤
