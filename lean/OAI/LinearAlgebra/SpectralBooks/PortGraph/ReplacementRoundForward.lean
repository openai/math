import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementCatalogueSlots
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoiceTag

/-! # Forward map for a catalogue choice on a certified representative

Choose one entry of the bounded tree catalogue at every canonical patch.
The two ends of each exterior wire retain the original vertex labels, slots,
and polarities. The occurrence of the old root marks its tree root role.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.ShapeCatalogue

open ReplacementTemplate ReplacementChoices

variable {F : Type} [Field F] {N K w c : ℕ} {ε : ℝ}
    (C : ShapeCatalogue F K w c) (S : System N K ε) (M : MapRep N)
    (t : (S.family C.Index).Label M)

abbrev forwardTag := S.choiceTag C.Index t

abbrev forwardPairing := S.choicePairing C.Index t C.templates (fun _ => Equiv.refl _)

abbrev forwardPieces := Forward.pieces (T := C.templates) (C.forwardTag S M t)

abbrev forwardLabel := Forward.label (T := C.templates) (C.forwardTag S M t)

/-- The tree root of the unique occurrence containing the old marked vertex. -/
def forwardRoot : StubPairing.Vertex (C.forwardPieces S M t) :=
  ⟨S.part M M.map.root,(C.templates (C.forwardTag S M t (S.part M M.map.root))).root⟩

local notation "pair" => C.forwardPairing S M t
local notation "tag" => C.forwardTag S M t

/-- The end of a retained cut wire lands in the occurrence of its old vertex. -/
theorem forward_end_occ (e : (pair).Wire) (b : Bool) :
    ((pair).ends (e,b)).1 = S.part M (M.map.graph.vertex e.val b) := by
  let P := S.partition M
  have hd := P.stubDart M.map (S.label M) (S.name M) (e,b)
  let d := (P.cutDarts M.map (S.label M) (S.name M)).symm (e,b)
  exact (P.owner_dart M.map (S.label M) (S.name M) d.1 d.2.val).symm.trans
    (congrArg (fun q : Fin M.edgeCount.val × Bool => S.part M (M.map.graph.vertex q.1 q.2)) hd)

theorem forward_reach : (pair).occurrenceGraph.ConnectedFrom (C.forwardRoot S M t).1 := by
  have eqGraph : (pair).occurrenceGraph = (M.map.graph.boundaryPairing (S.part M)).occurrenceGraph := by
    apply congrArg₂ PortGraph.mk
    · exact funext (fun e => C.forward_end_occ S M t e false)
    · exact funext (fun e => C.forward_end_occ S M t e true)
  rw [eqGraph]
  exact M.map.graph.boundaryPairing_connected (S.part M) (S.part_surjective M) M.map.connected

/-- The numbered replacement of a single old map and a complete choice of
tree-list indices, using the original cut wires and marked occurrence. -/
def forwardMap :=
  Forward.asMap tag pair C.portOrder C.degree (C.forwardRoot S M t) (C.forward_reach S M t)

theorem forward_portNumber (e : (pair).Edge (C.forwardPieces S M t)) (b : Bool) :
    (C.forwardMap S M t).portNumber e b = (endNumber (C.rules N ε).slot (Forward.namedEnd tag pair (e,b))).val := by
  rw [C.rules_slot]
  exact Forward.asMap_portNumber tag pair C.portOrder C.degree _ _ e b

private theorem record_root_iff (i : S.Occ M) :
    (∃ v, ((S.record M i).shape.typeAt v).root = true) ↔ i = S.part M M.map.root := by
  have eqSlot : (∃ v, ((S.record M i).shape.typeAt v).root = true) ↔
      ∃ v, PatchRecord.slots (S.block M i) (S.name M) v = M.map.root := by
    apply exists_congr
    intro v
    exact decide_eq_true_iff
  rw [eqSlot,PatchRecord.mem_slots_iff,S.mem_block]
  exact eq_comm

theorem forward_marked (v : StubPairing.Vertex (C.forwardPieces S M t)) :
    (C.rules N ε).marked (C.forwardLabel S M t v) ↔ v = (C.forwardMap S M t).root := by
  obtain ⟨i,v⟩ := v
  change (v = _ ∧ ∃ k, ((S.record M i).shape.typeAt k).root = true) ↔
    (⟨i,v⟩ : StubPairing.Vertex (C.forwardPieces S M t)) = C.forwardRoot S M t
  rw [record_root_iff]
  constructor
  · rintro ⟨hv,rfl⟩
    exact congrArg (Sigma.mk _) hv
  · intro he
    obtain rfl : i = S.part M M.map.root := congrArg Sigma.fst he
    exact ⟨(Sigma.mk.inj_iff.mp he).2.eq,rfl⟩

theorem forward_orient (e : (pair).Wire) (b : Bool) :
    (C.templates (tag ((pair).ends (e,b)).1)).direction ((pair).ends (e,b)).2 = b :=
  (S.partition M).orient M.map (S.label M) (S.name M) e b

theorem forward_identifiers : Function.Injective ((C.rules N ε).patchId ∘ tag) := by
  intro i j h
  apply Subtype.ext
  exact ((S.record_patch M i _).symm.trans h).trans (S.record_patch M j _)

/-- The labels and port numbers on a retained wire are precisely the two
old certificate values and the old slot at each of its endpoints. -/
theorem forward_oldEdge (e : (pair).Wire) :
    (C.rules N ε).oldEdge (Forward.liftTag tag _ ((pair).ends (e,false)))
      (Forward.liftTag tag _ ((pair).ends (e,true))) := by
  let P := S.partition M
  let j (b : Bool) := ((pair).ends (e,b)).1
  let d (b : Bool) := ((pair).ends (e,b)).2.val
  have hd (b : Bool) : P.oldDart M.map (S.label M) (S.name M) (j b) (d b) = (e.val,b) :=
    P.stubDart M.map (S.label M) (S.name M) _
  have owner (b : Bool) : P.vertexAt (S.name M) (j b) (d b).1 = M.map.graph.vertex e.val b :=
    (PatchRecord.actual_owner M.map _ (d b)).symm.trans
      (congrArg (fun q => M.map.graph.vertex q.1 q.2) (hd b))
  have number (b : Bool) : (d b).2.val = (M.map.slots _ ⟨(e.val,b),rfl⟩).val :=
    (PatchRecord.actual_slot M.map _ (d b)).symm.trans
      (congrArg (fun q => (M.map.slots _ ⟨q,rfl⟩).val) (hd b))
  change (MapLabels.tests N K ε).edge ((d false).2.castLE _) ((d true).2.castLE _)
    (S.label M (P.vertexAt (S.name M) (j false) (d false).1))
    (S.label M (P.vertexAt (S.name M) (j true) (d true).1))
  convert (S.pass M).2 e.val using 1
  · exact Fin.ext (number false)
  · exact Fin.ext (number true)
  · exact congrArg (S.label M) (owner false)
  · exact congrArg (S.label M) (owner true)

set_option maxHeartbeats 1200000 in
/-- Every forward choice passes the catalogue's actual small-map decoder. -/
theorem forward_accepts : (C.rules N ε).Accepts (C.forwardMap S M t) (C.forwardLabel S M t) :=
  Forward.asMap_accepts tag pair C.portOrder C.degree _ _ _ C.rules_slot
    (fun _ => trivial) (C.forward_marked S M t) (C.forward_orient S M t)
    (C.forward_identifiers S M t) (C.forward_oldEdge S M t)

/-- In the concrete catalogue the stub names of each term are already the
stub names of the old record. -/
theorem forwardPairing_eq : C.forwardPairing S M t = S.pairing M := by
  rfl

/-- The separated cut budget gives the exact vertex bound for one round. -/
theorem forward_cap {a : ℕ} (ha : 0 < a) (hε : ε = 1 / (2 * (a : ℝ))) :
    Fintype.card (StubPairing.Vertex (C.forwardPieces S M t)) ≤ max 1 (N/a) := by
  apply (pair).card_assemble_le_of_cut_budget (C.forwardPieces S M t) ha
    (show Fintype.card (Fin M.vertexCount.val) ≤ N by simpa using Nat.le_of_lt_succ M.vertexCount.isLt)
    (C.forward_reach S M t) (fun j => (C.selected (tag j)).roles_le)
  let e : (pair).Wire ≃ M.map.graph.CrossEdge (S.part M) := Equiv.refl _
  rw [← hε, Fintype.card_congr e]
  exact S.cut_budget M

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
