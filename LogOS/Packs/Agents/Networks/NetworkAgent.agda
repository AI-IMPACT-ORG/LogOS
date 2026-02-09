{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Networks.NetworkAgent where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Minimal.ConAlg using (ConAlg)
open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
open import LogOS.Packs.Agents.Networks.Hetero using (AgentNetwork)
import LogOS.Minimal.View as View

-- Network-as-agent view:
-- choose a hub role, translate all role constraints to the hub, then aggregate.
--
-- There is no canonical aggregation; it is an explicit parameter. Any claim
-- about “the network as an agent” therefore depends on the chosen aggregator.
-- The record also requires aggregation to respect the hub’s observational
-- mutual refinement (`Obs≈`), ensuring observable behavior is well-defined.
-- (The `_↔_`-presentation `ObsEqOn` is kept as a logically equivalent alias.)

record NetworkAgent {ℓ ℓTask ℓRole : Level} (Role : Set ℓRole)
  : Set (lsuc (lsuc (ℓ ⊔ ℓTask ⊔ ℓRole))) where

  -- Aggregation is required to respect observational mutual refinement at the hub.
  -- This makes the “network-as-agent” view well-defined up to the hub’s
  -- observable boundary behavior.
  AggRespectsObsEqAt
    : (Net : AgentNetwork {ℓ} {ℓTask} Role)
    → (hub : Role)
    → (aggregate : (Role → AgentNetwork.Con Net hub) → AgentNetwork.Con Net hub)
    → Set (ℓ ⊔ ℓRole)
  AggRespectsObsEqAt Net hub aggregate =
    ∀ {f g}
    → (∀ r → Prop.ObsEqOn (AgentNetwork.Sat Net hub) (f r) (g r))
    → Prop.ObsEqOn (AgentNetwork.Sat Net hub) (aggregate f) (aggregate g)

  -- Canonical form: extensionality w.r.t. observational mutual refinement.
  AggRespectsObs≈At
    : (Net : AgentNetwork {ℓ} {ℓTask} Role)
    → (hub : Role)
    → (aggregate : (Role → AgentNetwork.Con Net hub) → AgentNetwork.Con Net hub)
    → Set (ℓ ⊔ ℓRole)
  AggRespectsObs≈At Net hub aggregate =
    ∀ {f g}
    → (∀ r → View.Obs≈ (AgentNetwork.Sat Net hub) (f r) (g r))
    → View.Obs≈ (AgentNetwork.Sat Net hub) (aggregate f) (aggregate g)

  AggRespectsObsEqAt↔AggRespectsObs≈At
    : ∀ {Net hub aggregate}
    → AggRespectsObsEqAt Net hub aggregate
      ↔ AggRespectsObs≈At Net hub aggregate
  AggRespectsObsEqAt↔AggRespectsObs≈At {Net} {hub} {aggregate} =
    let SatHub = AgentNetwork.Sat Net hub in
    Prop.intro
      (λ extEq {f} {g} fg≈ →
        Prop.to (View.ObsEqOn↔Obs≈ SatHub {x = aggregate f} {y = aggregate g})
          (extEq (λ r →
            Prop.from (View.ObsEqOn↔Obs≈ SatHub {x = f r} {y = g r}) (fg≈ r))))
      (λ ext≈ {f} {g} fgEq →
        Prop.from (View.ObsEqOn↔Obs≈ SatHub {x = aggregate f} {y = aggregate g})
          (ext≈ (λ r →
            Prop.to (View.ObsEqOn↔Obs≈ SatHub {x = f r} {y = g r}) (fgEq r))))

  field
    Net       : AgentNetwork {ℓ} {ℓTask} Role
    hub       : Role
    edgeToHub : (r : Role) → AgentNetwork.Edge Net r hub
    aggregate : (Role → AgentNetwork.Con Net hub) → AgentNetwork.Con Net hub
    aggregate-respects-Obs≈ : AggRespectsObs≈At Net hub aggregate

  open AgentNetwork Net public

  AggRespectsObsEq : Set (ℓ ⊔ ℓRole)
  AggRespectsObsEq = AggRespectsObsEqAt Net hub aggregate

  AggRespectsObs≈ : Set (ℓ ⊔ ℓRole)
  AggRespectsObs≈ = AggRespectsObs≈At Net hub aggregate

  aggregate-respects-obsEq : AggRespectsObsEq
  aggregate-respects-obsEq =
    Prop.from (AggRespectsObsEqAt↔AggRespectsObs≈At {Net = Net} {hub = hub} {aggregate = aggregate})
      aggregate-respects-Obs≈

  socket : AgentSocket (Sig hub) (Q hub) (Task hub)
  socket = Sock hub

  open AgentSocket socket public hiding (conAlg)

  toHub : (r : Role) → Con r → Con hub
  toHub r = AgentNetwork.Edge.translateCon (edgeToHub r)

  aggregated : Policy → Con hub
  aggregated pol = aggregate (λ r → toHub r (pol r))

  -- Canonical aggregation: fold the hub tensor over a chosen list of roles.
  --
  -- This is an opt-in default; callers can use any enumeration of roles and
  -- supply the tensor compatibility hypothesis explicitly.

  tensorAggregate
    : List Role
    → (Role → Con hub)
    → Con hub
  tensorAggregate [] f =
    let open ConAlg (conAlg hub) using (I∂) in
    I∂
  tensorAggregate (r ∷ rs) f =
    tensorAt hub (f r) (tensorAggregate rs f)

  abstract
    tensorAggregate-respects-obsEq
      : (roles : List Role)
      → (tensor-respects-obsEq
          : ∀ {a b c d}
          → Prop.ObsEqOn (Sat hub) a b
          → Prop.ObsEqOn (Sat hub) c d
          → Prop.ObsEqOn (Sat hub) (tensorAt hub a c) (tensorAt hub b d))
      → AggRespectsObsEqAt Net hub (tensorAggregate roles)
    tensorAggregate-respects-obsEq [] tensor-respects eqs =
      let open ConAlg (conAlg hub) using (I∂) in
      Prop.ObsEqOn-refl (Sat hub) I∂
    tensorAggregate-respects-obsEq (r ∷ rs) tensor-respects eqs =
      tensor-respects (eqs r) (tensorAggregate-respects-obsEq rs tensor-respects eqs)

    tensorAggregate-respects-Obs≈
      : (roles : List Role)
      → (tensor-respects-obsEq
          : ∀ {a b c d}
          → Prop.ObsEqOn (Sat hub) a b
          → Prop.ObsEqOn (Sat hub) c d
          → Prop.ObsEqOn (Sat hub) (tensorAt hub a c) (tensorAt hub b d))
      → AggRespectsObs≈At Net hub (tensorAggregate roles)
    tensorAggregate-respects-Obs≈ roles tensor-respects =
      Prop.to (AggRespectsObsEqAt↔AggRespectsObs≈At {Net = Net} {hub = hub} {aggregate = tensorAggregate roles})
        (tensorAggregate-respects-obsEq roles tensor-respects)
