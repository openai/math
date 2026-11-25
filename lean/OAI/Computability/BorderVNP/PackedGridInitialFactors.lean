import OAI.Computability.BorderVNP.PackedGridDirectory
import OAI.Computability.BorderVNP.PackedGridBatch
import OAI.Computability.BorderVNP.ParseBatchInitialTags

/-! # Boolean and unary rows of the initial polynomial batch

Only the designated unary vertices compare a selected wire to an externally reported
use. At all other sites the one-copy truth table is the actual Boolean constraint of
the query verifier. The factor's response is checked against the manuscript's tagged
leaf at that same site and assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse Diagonal.CellEntries
open scoped Classical

/-- Acceptance of an initial factor on named lanes and reported unary bits. -/
def Rule.passes {D : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits} {v : N.Site} :
    Rule N v → (CellBox.Lane N v → Bool) → (Port → Bool) → Bool
  | .truth f, read, _ => f read
  | .unary l port, read, use => read l == use port

/-- The private box checker evaluates the rule on exactly the lane and report addresses
appearing in its public repeat record. -/
theorem accepts_passes {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {C : Type} (cell : N.Site → C) (c : C) {m n : ℕ} (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (v : {v : N.Site // cell v = c}) (bank : ℕ → Bool) (off copy : ℕ) (r : Rule N v.val) :
    accepts N cell c edgeID portID v bank off copy r =
      r.passes (fun l => bank (off+(lane N cell c edgeID portID v l).val))
        (fun p => bank (p.atBit copy 0)) := by cases r <;> rfl

/-- The signed coefficient calculation will tally true reports by their parameter and
power-bit index. Initial Boolean leaves are evaluated directly. -/
def leafPass {A : Type*} (report : A → ℕ → Port) (use : Port → Bool) : Leaf A Empty → Bool
  | .check ok => ok
  | .power p i yes => yes == use (report p i)
  | .scalar g => g.elim

open VPVNP VPVNP.VerifierNetwork ParseBatch ParseBatchTrees ParseBatchVerifier
variable {m g n r : ℕ} (d : Fin n) (trees : Frame (BatchPins m g n r d) Unit)
variable (report : GrammarLabel (Fin m × Bool) (Fin g) n → ℕ → Port)

/-- The sparse descriptor for an actual original batch site. Both the unary location
and its selected input lane use the verifier network's specified embeddings. -/
noncomputable def queryRule (v : (queryLayout d trees).Site) : Rule (queryLayout d trees).network v :=
  if hw : ∃ j : WeightSites m g r d, BooleanLayout.weightSite (verifier d trees) weightedPin j = v then
    let j := hw.choose
    let edge := BooleanLayout.weightEdge (verifier d trees) weightedPin j
    let hd := (BooleanLayout.weightEdge_dst (verifier d trees) weightedPin j).trans hw.choose_spec
    .unary (.inl ⟨⟨edge, Or.inr hd⟩,0⟩) (report j.1 j.2.val)
  else
    .truth (fun read => (CellBox.localRow (queryLayout d trees).network
      (initialLeaf (Gadget := Empty) d trees) v read).accepted)

/-- The actual private factor succeeds exactly on passing Boolean rows and correctly
reported selected unary uses, at their original parameter and count-bit indices. -/
theorem queryRule_passes (v : (queryLayout d trees).Site)
    (read : CellBox.Lane (queryLayout d trees).network v → Bool) (use : Port → Bool) :
    (queryRule d trees report v).passes read use =
      leafPass report use (CellBox.localRow (queryLayout d trees).network
        (initialLeaf (Gadget := Empty) d trees) v read) := by
  by_cases h : ∃ j : WeightSites m g r d, BooleanLayout.weightSite (verifier d trees) weightedPin j = v
  · simp only [queryRule,h,dite_true,Rule.passes,CellBox.localRow,initialLeaf,leafPass]
  · simp only [queryRule,h,dite_false,Rule.passes,CellBox.localRow,initialLeaf,leafPass,Leaf.accepted]

end Packing.GridBoxes

end BorderVNP
end Computability
end OAI
