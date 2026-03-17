{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Kernel where

-- Curated kernel-level surface for the LT core.
--
-- Reading:
-- - coherence: refinement < guarded refinement
-- - architecture: explicit observation + boundary transport
-- - implementation: displayed code witnesses over architectural maps
-- - façade: stable `KernelHom` / `LOG` surface and derived stacks

module Architecture where
  open import LogOS.LT.View public
  open import LogOS.LT.View.Roles public
  open import LogOS.LT.Kernel public
  open import LogOS.LT.BoundaryHom public
  open import LogOS.LT.LOG.Boundary2Cat public

  LOGArchitecture = LOGᴳ

module Implementation where
  open import LogOS.LT.BoundaryImplementation.Core public
  open import LogOS.LT.LOG.Implementation2Cat.Core public

module ImplementationView where
  import LogOS.LT.Hom as Hom
  import LogOS.LT.Hom.Reasoning as HomReasoningKit
  open Hom public using
    ( obs
    ; obsView
    ; obsView≈transportView
    ; _⇒_
    ; ⇒→⇒∂
    ; ⇒∂→⇒
    ; ⇒↔⇒∂
    ; whiskerL
    ; whiskerR
    )
  module ImplementationReasoning = HomReasoningKit.ImplementationReasoning

module Coherence where
  open import LogOS.LT.Coherence public using
    ( CohMode
    ; CohRel
    ; approx
    ; under
    )

module Facade where
  import LogOS.LT.Hom as Hom
  import LogOS.LT.Hom.Reasoning as HomReasoningKit
  open Hom public using
    ( BoundaryImplementation
    ; implementCode
    ; decode-implementsBoundary
    ; idBoundaryImplementation
    ; composeBoundaryImplementation
    ; KernelHomLike
    ; KernelHomLikeR
    ; toKernelHomLikeR
    ; fromKernelHomLikeR
    ; boundaryPart
    ; implementationPart
    ; mkKernelHomParts
    ; KernelHom≈
    ; KernelHom⊑
    ; KernelHom
    ; BehavioralKernelHom
    ; UnderApproxKernelHom
    ; map∂
    ; map∂-mono
    ; mapCode
    ; decode-mapCode
    ; decode-mapCode≈
    ; decode-mapCode⊑
    ; idKernelHomLike
    ; _∘Like_
    ; idKernelHom
    ; _∘_
    ; transportObs
    ; transportView
    ; _⇒∂_
    ; whiskerL∂
    ; whiskerR∂
    )
  module HomReasoning = HomReasoningKit.HomReasoning
  open import LogOS.LT.LOG.Kernel2Cat public
  open import LogOS.LT.LOG.GuardedKernel2Cat public using (KernelHomPreorder⊑; LOG⊑; LOGGuarded)

module Guarded where
  open import LogOS.API.Guarded public

-- Core kernel / boundary interface
-- Use this flat export block when you want the whole curated kernel surface;
-- the local modules above are the quicker way to navigate by theme.
open import LogOS.LT.View public
open import LogOS.LT.View.Roles public
open import LogOS.LT.Kernel public
  using (Kernel; bnd; Code; decode; kernelFromView; decodeView; EncodePort; encode; BoundaryKernel; CodePreorder; ObservedCodePreorder; Kernel×)
open import LogOS.LT.BoundaryHom public using (BoundaryHom; idBoundaryHom; _∘∂_)
import LogOS.LT.Hom as Hom
import LogOS.LT.Hom.Reasoning as HomReasoningKit
open Hom public using
  ( BoundaryImplementation
  ; implementCode
  ; decode-implementsBoundary
  ; idBoundaryImplementation
  ; composeBoundaryImplementation
  ; KernelHomLike
  ; KernelHomLikeR
  ; toKernelHomLikeR
  ; fromKernelHomLikeR
  ; boundaryPart
  ; implementationPart
  ; mkKernelHomParts
  ; KernelHom≈
  ; KernelHom⊑
  ; KernelHom
  ; BehavioralKernelHom
  ; UnderApproxKernelHom
  ; map∂
  ; map∂-mono
  ; mapCode
  ; decode-mapCode
  ; decode-mapCode≈
  ; decode-mapCode⊑
  ; idKernelHomLike
  ; _∘Like_
  ; idKernelHom
  ; _∘_
  ; transportObs
  ; transportView
  ; _⇒∂_
  ; whiskerL∂
  ; whiskerR∂
  )
module HomReasoning = HomReasoningKit.HomReasoning
open import LogOS.LT.LOG.Boundary2Cat public using (LOGᴳ; LOGᴳLaws; BoundaryHomL; _⇒ᴳ_; restrict⇒ᴳ)
open import LogOS.LT.LOG.Implementation2Cat public
open import LogOS.LT.LOG.Kernel2Cat public
open import LogOS.LT.LOG.GuardedKernel2Cat public using (KernelHomPreorder⊑; LOG⊑; LOGGuarded)
-- Closure / iteration / reflection
open import LogOS.LT.Iteration public
open import LogOS.LT.Flow public
open import LogOS.LT.AbstractNucleus public
open import LogOS.LT.Sup.FinSup public
open import LogOS.LT.Sup.AbstractSigmaDCPO public
open import LogOS.LT.Sup.SupOmega public
open import LogOS.LT.Sup.AbstractKleene public
open import LogOS.LT.Sup.AbstractCoKleene public
open import LogOS.LT.Sup.AbstractGeneratedClosure public
open import LogOS.LT.Reflection public
open import LogOS.LT.Contracts public
open import LogOS.LT.Presentation public
-- Generated image / generated subobject surfaces
open import LogOS.LT.Presentation.GeneratedImage public
  renaming (module For to GeneratedImageFor)
  using
  ( StrictGeneratedImages
  ; GeneratedImages
  ; generateImage
  ; intoGeneratedImage
  ; intoGeneratedImage≈
  ; outOfGeneratedImage
  ; outOfGeneratedImage≈
  ; strictGeneratedImages
  )
open import LogOS.LT.Presentation.GeneratedSubobject.Core public
  renaming (module For to GeneratedSubobjectFor)
  using
  ( StrictLocalGenerators
  ; LocalGenerators
  ; StrictGeneratedSubobjects
  ; GeneratedSubobjects
  ; SmallClassifier
  ; Ix
  ; elemAt
  ; memberIn
  ; memberIn≈
  ; memberOut
  ; memberOut≈
  ; generate
  ; classifiedGenerate
  ; intoGenerated
  ; intoGenerated≈
  ; outOfGenerated
  ; outOfGenerated≈
  ; strictLocalGenerators
  ; strictGeneratedSubobjects
  )
-- Stage and section structure
open import LogOS.LT.Stage.SuccessorChain public using (SuccessorChain; StageOf; next; levelChain)
open import LogOS.LT.Stage.Section public using (Section; at)
open import LogOS.LT.DisplayedThin2Cat.SuccessorStage public using (SuccessorStage)
-- Port signatures and stack discipline
open import LogOS.LT.Ports.PortSig public using
  ( PortSig
  ; PortEntry
  ; mkEntry
  ; sig
  ; TagTy
  ; Tagℓ
  )
import LogOS.LT.Ports.PortStack as PortStack
import LogOS.LT.Ports.PortStack.Unique as PortStackUnique
open import LogOS.LT.Ports.PortStack public using (NoDupStack)
open import LogOS.LT.Ports.PortStack.Unique public using
  ( UniquePort
  ; mkUniquePort
  ; UniquePortStack
  ; mkUniquePortStack
  ; uniqueHasPort
  ; uniqueMember
  ; noDupSingleton
  ; singletonUniqueStack
  )
module UniqueInstances = PortStackUnique.UniqueInstances

open import LogOS.LT.Discipline.PortStackFolding public renaming (ok to ltPortStackFolding-ok)
open import LogOS.LT.Discipline.SuccessorStageFolding public renaming (ok to ltSuccessorStageFolding-ok)
open import LogOS.LT.Discipline.HomDefaults public renaming (ok to ltHomDefaults-ok)
open import LogOS.LT.Discipline.ArchitectureImplementationLaw public
  renaming (ok to ltArchitectureImplementationLaw-ok)
