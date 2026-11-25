import OAI.Hierarchy.DescentHubSeedHistory
import OAI.Hierarchy.DescentNativeInput

namespace OAI
/-! # One immutable recipe dictionary for every original stack and census choice -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentInitialHost DescentPhysicalSplit DescentSixParty
open scoped Classical BigOperators
noncomputable section
variable {J P Tag F : Type} [Field F] {d : ℕ} [Fintype J]
variable {width : P→ℕ} (W : J→World F d P width) (read : Tag→List (List Bool)→F)
variable (r : ∀j v,Recipe Tag (Boundary (W j).graph v))

def blockBoundary (j : J) (v : (W j).graph.Site) : Boundary (W j).graph v→Boundary (blockGraph W) ⟨j,v⟩
  | .inl e=>.inl ⟨⟨j,e.val⟩,e.property.imp (congrArg (Sigma.mk j)) (congrArg (Sigma.mk j))⟩
  | .inr p=>.inr ⟨⟨j,p.val⟩,congrArg (Sigma.mk j) p.property⟩

def groupedRecipe (u : (blockGraph W).Site) :=
  rewire (r u.1 u.2) (blockBoundary W u.1 u.2)

theorem grouped_represents (valid : ∀i,Represents (W i).graph read (W i).tables (r i)) :
    Represents (blockGraph W) read (blockTables W) (groupedRecipe W r) := by
  rintro ⟨i,v⟩ z x
  let localWire (e : Incident (W i).graph v) :=
    z ⟨⟨i,e.val⟩,e.property.imp (congrArg (Sigma.mk i)) (congrArg (Sigma.mk i))⟩
  let localPin (p : Attached (W i).graph v) :=
    x ⟨⟨i,p.val⟩,congrArg (Sigma.mk i) p.property⟩
  refine (rewire_value read (r i v) (blockBoundary W i v) (input (blockGraph W) z x)).trans ?_
  refine Eq.trans ?_ (valid i v localWire localPin)
  apply congrArg ((r i v).value read)
  funext q
  cases q <;> rfl

open Catalyst CorrectionBatch
variable {k p : ℕ} (X : Approximation F k p) (R s : ℕ) (c : (initialGroup X R s).Choice)
private abbrev seedComponent (j : Fin R) :=
  ((Histories.seedInternal (markedInput X) s
    (Sum.elim (fun _ : X.network.copyGraph.Site => true) (fun _ => false))).state (c j)).toWorld

private abbrev seedComponentRecipe (j : Fin R) :=
  seedHistory X.network.copyGraph X.network.copyTable (markedInput X).core s (physical_output X).1 (c j)

def initialRecipe := groupedRecipe (seedComponent X R s c) (seedComponentRecipe X R s c)

theorem source_represents : Represents ((initialGroup X R s).state c).graph seedRead
    ((initialGroup X R s).state c).tables (initialRecipe X R s c) :=
  grouped_represents (seedComponent X R s c) seedRead (seedComponentRecipe X R s c) (fun j =>
    hub_seed_represents X.network.copyGraph X.network.copyTable (markedInput X).core s (physical_output X).1 (c j))

end
end Hierarchy.DescentKernelHistory

end OAI
