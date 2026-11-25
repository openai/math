import OAI.Hierarchy.DescentNetworkWorld
import OAI.Hierarchy.DescentColonies

namespace OAI
/-! # Integer site loads and hub incidence before an ordinary step -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing DescentColonies
open scoped BigOperators Classical
noncomputable section

namespace MarkedWorld
variable {F : Type*} [Field F] {d : ℕ} {P : Type*} {bits : P→ℕ}

/-- Core cables join two nonhubs; every other physical cable is a tether between a hub and a nonhub. -/
structure HubIncidence (A : MarkedWorld F d P bits) (hub : A.graph.Site→Bool) : Prop where
  inside : ∀e∈A.core,hub (A.graph.src e)=false ∧ hub (A.graph.dst e)=false
  outside : ∀e∉A.core,hub (A.graph.src e)≠hub (A.graph.dst e)

variable {D : ℕ} {Aty : Type*}
variable (W : MarkedWorld F D P bits) (hub : W.graph.Site → Bool)
variable (atoms : W.graph.Site → List Aty) (wire β hist : ℕ)

/-- Record both endpoint occurrences with their fixed hub multiplicities,
and the history words stored at the actual site. -/
def siteUnits (v : W.graph.Site) : ℕ :=
  (∑e, if v=W.graph.src e then wire*W.graph.width e*(if hub (W.graph.src e) then β else 1) else 0) +
  (∑e, if v=W.graph.dst e then wire*W.graph.width e*(if hub (W.graph.dst e) then β else 1) else 0) +
  hist*(atoms v).length

end MarkedWorld

namespace StarKeys
variable {V : Type} [Fintype V] [DecidableEq V] {k d : ℕ} {P : Type*} {bits : P→ℕ}
variable (N : Network d P bits) (pos : N.Site → V) (block : N.Site → Block k) (full : N.Site → ℕ)

/-- The actual sites may occupy a strict subset of the common host. Multiple
sites at the same tentative address are charged by their whole combined load. -/
def blockMass (v : V) (x : Block k) := ∑u : N.Site, if pos u=v ∧ block u=x then full u else 0

end StarKeys
end
end Hierarchy.DescentSixParty

end OAI
