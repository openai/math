import OAI.Hierarchy.DescentSeedGroupHistory
import OAI.Hierarchy.DescentSeedRootRows
import OAI.Hierarchy.DescentRecordedHistory
import OAI.Hierarchy.DescentHistoryLanes
import OAI.Hierarchy.DescentNormalize
import OAI.Hierarchy.DescentNamedBoundary

namespace OAI
/-! # Typed scalar history for every branch of the actual normalized shrink step -/

namespace Hierarchy.DescentKernelHistory
open DescentSixParty DescentHostDirectory Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {d : ℕ} {P : Type} {bits : P→ℕ}

structure Description (W : MarkedWorld F d P bits) where
  Tag : Type
  scalar : Tag→List (List Bool)→F
  recipe : ∀v,Recipe Tag (Boundary W.graph v)
  correct : Represents W.graph scalar W.tables recipe

namespace Description
variable {W : MarkedWorld F d P bits} (H : Description W)

def selected {I C : Type} [Fintype I] (G : PoweredGadget F) (pick : I×Fin 2↪W.graph.Edge)
    (z : I→ℕ) (hz : ∀i,0<z i) (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b)
    {Z : ℕ} (room : ∀i,z i≤Z) (pack : W.graph.Site→C) (p : I→Profile G.C) :
    Description (W.selected G pick z hz fit pack p) where
  Tag := H.Tag⊕GadgetTag G Z
  scalar := Sum.elim H.scalar (gadgetScalar G)
  recipe := recordedRecipe G W.toWorld pick z hz fit room pack p H.recipe
  correct := recorded_represents G W.toWorld pick z hz fit room pack p H.recipe H.scalar H.correct

def coalesced {V : Type} [DecidableEq V] (key : W.graph.Site→Key V)
    (hub : V→Bool) (k g : ℕ) : Description (W.coalesced key hub k g) := by
  let site := MarkedWorld.address W key hub k g
  let pos := fun _ : MarkedWorld.reclaimed W key hub k g => (0 : EuclideanSpace ℝ (Fin d))
  have ball (v : MarkedWorld.reclaimed W key hub k g) : ‖pos v‖ ≤ 1 := by
    simp [pos]
  exact ⟨H.Tag,H.scalar,quotientRecipe W.graph site pos ball H.recipe,
    quotient_represents W.graph H.scalar site pos ball W.tables H.recipe H.correct⟩

def pieces (m : W.graph.Edge→ℕ) (q : ℕ) (fit : ∀e∈W.core,W.graph.width e=m e*q) :
    Description (W.pieces q m fit) where
  Tag := H.Tag×List ℕ
  scalar := laneScalar H.scalar
  recipe := fun v=>splitLanes (H.recipe v) (laneNames W.graph W.core m q v)
  correct := split_represents H.scalar W.graph W.core m q fit W.tables H.recipe H.correct

def renamed (s : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge) : Description (PhysicalRename.world W s e) where
  Tag := H.Tag
  scalar := H.scalar
  recipe v := rewire (H.recipe (s.symm v)) (PhysicalRename.boundary W.graph s e v)
  correct := PhysicalRename.represents W.graph s e H.scalar W.tables H.recipe H.correct

def follow {W : MarkedWorld F d P bits} (update : Normalize W) :
    Description W→Description update.result := by
  induction update with
  | done => exact id
  | named _ s e _ ih => exact fun h => ih (h.renamed s e)
  | split _ q m fit _ ih => exact fun h => ih (h.pieces m q fit)
  | merge _ V key flag k g _ ih => exact fun h => ih (h.coalesced (V := V) key flag k g)

open DescentInitialHost Catalyst
def initial {k p : ℕ} (X : Approximation F k p) (R s : ℕ) (c : (initialGroup X R s).Choice) :
    Description ((initialGroup X R s).state c) :=
  ⟨SeedTag s,seedRead,initialRecipe X R s c,source_represents X R s c⟩

end Description
end
end Hierarchy.DescentKernelHistory

end OAI
