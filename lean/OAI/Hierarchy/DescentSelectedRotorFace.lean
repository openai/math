import OAI.Hierarchy.DescentRotorFlatPhysical
import OAI.Hierarchy.DescentCalendarPublicSocketField

namespace OAI
/-! Recover the signed face and the physical layer/batch of any issued private rotor slot. -/
namespace Hierarchy.DescentRotorOperandQueryROM.Shape
open DescentLaneGates DescentPhysicalSplit DescentBatchedNodeOrder DescentRotor DescentResetLaneIssue
open DescentRotorOperandTicket LinearAlgebra.SpectralBooks ThreeFlat
open RouteUnits Expander NonlinearExpanders
open scoped Classical
noncomputable section
variable {n h : ℕ} (G : Graph n h) (C : Shape)
local notation "Q" => DescentCommonPalette.rotor G
local notation "H" => Physical.host G.arcs 0 0 0 0 0

private def isAt (levels : ℕ) (site : (Q).Site) (l : PrivateLane G) : Prop :=
  endpoint H l.face l.edge=site ∧
    ∃r:Fin levels,∃b:Fin C.batches,l.address=r.val*C.batches+b.val

private theorem spine_at (mult levels p : ℕ) (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count H v))
    (s : Bool) (t : SpineRow (r:=levels) (m:=C.batches) (C.subrow G mult v)) :
    isAt G C levels ⟨v,.inr i⟩ (C.spineReference G mult levels p v i s t):=by
  refine ⟨?_,t.2.1,t.2.2.1,rfl⟩
  cases s
  · exact fore_face H v i
  · exact back_face H v i

private theorem row_at (mult levels p node : ℕ) (site : (Q).Site) (l : PrivateLane G)
    (member_ : l∈C.privateRows G mult levels p node site) : isAt G C levels site l:=by
  rcases site with ⟨v,side|i⟩
  · cases side
    · simp only [privateRows] at member_
      split at member_
      next live =>
        obtain ⟨j,rfl⟩:=List.mem_ofFn.mp member_
        let rb : Fin levels×Fin C.batches:=finProdFinEquiv.symm ⟨node,live⟩
        exact ⟨root_face H v,rb.1,rb.2,rfl⟩
      · simp at member_
    · simp [privateRows] at member_
  · simp only [privateRows] at member_
    split at member_
    · split at member_
      next spine _ =>
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member_
        rcases member_ with rfl|rfl <;> exact spine_at G C mult levels p v i _ spine
      next t _ =>
        cases chosen : name H v i with
        | inl pin =>
          simp only [chosen,List.mem_singleton] at member_
          subst l
          exact spine_at G C mult levels p v i true ⟨i,t⟩
        | inr slot =>
          rcases slot with ⟨e,dir⟩
          simp only [chosen,List.mem_cons,List.not_mem_nil,or_false] at member_
          rcases member_ with rfl|rfl
          · exact spine_at G C mult levels p v i true ⟨i,t⟩
          · exact ⟨supply_face H v i e dir chosen,t.1,t.2.1,rfl⟩
    · simp at member_

/-- The actual list index, including repeated words of a strided lane, recovers
both the installed endpoint and its registered layer/batch address. -/
theorem flattened_face (mult levels p node : ℕ) (site : (Q).Site) (arg : ℕ)
    (l : PrivateLane G) (within : ℕ) (fetch : (C.flattened G mult levels p node site)[arg]?=some (l,within)) :
    endpoint H l.face l.edge=site ∧
      ∃r:Fin levels,∃b:Fin C.batches,l.address=r.val*C.batches+b.val:=by
  have entry:=List.mem_of_getElem? fetch
  change (l,within)∈(_ : List _).flatMap _ at entry
  obtain ⟨row,present,inside⟩:=List.mem_flatMap.mp entry
  obtain ⟨j,eqn⟩:=List.mem_ofFn.mp inside
  change (row,j.val)=(l,within) at eqn
  cases eqn
  exact row_at G C mult levels p node site _ present

end
end Hierarchy.DescentRotorOperandQueryROM.Shape

end OAI
