import OAI.Computability.BorderVNP.CrossingNetwork

namespace OAI
/-! # Finite physical tensor worlds and their marked wire accounts -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {D : ℕ} {P : Type*} {bits : P→ℕ}

/-- The graph and its complete local tables after a physical contraction.
Public pin values, including catalyst pins, retain their original names. -/
structure World (F : Type*) (D : ℕ) (P : Type*) (bits : P → ℕ) where
  graph : Network D P bits
  tables : graph.Tables F

def World.value (A : World F D P bits) := A.graph.value A.tables

def World.coreWidth (A : World F D P bits) := ∑ e,A.graph.width e

structure MarkedWorld (F : Type*) (D : ℕ) (P : Type*) (bits : P → ℕ) extends World F D P bits where
  core : Finset graph.Edge

namespace MarkedWorld
variable (A : MarkedWorld F D P bits)
def liveWidth := ∑e∈A.core,A.graph.width e
def tetherWidth := ∑e∈A.coreᶜ,A.graph.width e

end MarkedWorld
end
end Hierarchy.DescentSixParty

end OAI
