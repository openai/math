import OAI.Computability.BorderVNP.TeamTapeInputRoute
import OAI.Computability.VPVNP.RAMSharedFields

/-! # Exact wire positions of the virtual sorting exchanges

There is one variable per internal boundary-record bit and one per source/layer/block bit.
The opposite endpoint names the same XOR-partner send. Missing boundary ports are physical
zero fields and introduce no summation variable. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.Wires

open VPVNP BurstRAM RAMLayout RAMTape RAMSerialization RAMBoundary
open TeamTapeSorting (Fields embedFields incoming outgoing)
open TeamTapeInputRoute (comparisonSize comparisonBits rowBits)
open RAMTape.Boundary (recordBytes)

/-- One actual sender for each physical sorting or interblock boundary bit. -/
abbrev SortEdge (d e W : ℕ) :=
  (Fin (2^d-1) × Fin (5*W)) ⊕ (Layer d × (Word d × Fin (blockBits (2^e) W)))

variable {d e W : ℕ}

/-- Unrestricted assignments to precisely the real sorting wires are in bijection with
the two typed families of raw fields, including invalid record tags. -/
def sortEquiv : (SortEdge d e W → Bool) ≃ Fields d e W where
  toFun f := (fun u => (arrayBits 5 W).symm (fun i => f (.inl (u,i))),
    fun l v j => f (.inr (l,v,j)))
  invFun a
    | .inl (u,j) => arrayBits 5 W (a.1 u) j
    | .inr (l,v,j) => a.2 l v j
  left_inv f := by
    funext i; rcases i with ⟨u,j⟩ | ⟨l,v,j⟩
    · change arrayBits 5 W ((arrayBits 5 W).symm _) j = _
      rw [Equiv.apply_symm_apply]
    · rfl
  right_inv a := by
    apply Prod.ext
    · funext u; exact (arrayBits 5 W).symm_apply_apply _
    · rfl

/-- Incoming predecessor and outgoing successor boundary slots, including their zero clamps. -/
def boundarySlot (before : Bool) (v : Word d) (j : Fin (5*W)) : Option (SortEdge d e W) :=
  if before then
    if h : 0 < v.val then some (.inl (⟨v.val-1,by have := v.isLt; omega⟩,j)) else none
  else if h : v.val+1 < 2^d then some (.inl (⟨v.val,by omega⟩,j)) else none

private theorem recordBytes_raw (s : Fin 5 → Word W) :
    recordBytes s = List.ofFn (arrayBits 5 W s) := by
  have h := (SuccessorFields.raw_eq_flatten_words (arrayBits 5 W s)).symm
  simpa only [Boundary.recordBytes,Boundary.recordWords,Equiv.symm_apply_apply] using h

private theorem zeros_at (i : Fin (5*W)) : arrayBits 5 W (fun _ => 0) i = false := by
  obtain ⟨⟨j,k⟩,rfl⟩ := finProdFinEquiv.surjective i
  rw [arrayBits_at,wordBits_zero]

private theorem boundary_read (f : SortEdge d e W → Bool) (before : Bool) (v : Word d) :
    List.ofFn (fun j => (boundarySlot before v j).elim false f) =
      recordBytes (if before then incoming (sortEquiv f) v else outgoing (sortEquiv f) v) := by
  rw [recordBytes_raw]
  apply congrArg List.ofFn
  funext i
  cases before
  · by_cases h : v.val+1 < 2^d
    · simp [boundarySlot,TeamTapeSorting.outgoing,h,sortEquiv]
    · simp [boundarySlot,TeamTapeSorting.outgoing,h,zeros_at]
  · by_cases h : 0 < v.val
    · simp [boundarySlot,incoming,h,sortEquiv]
    · simp [boundarySlot,incoming,h,zeros_at]

private def incidentIndex (i : Fin (comparisonSize d e W)) : Fin (width d (2^e) W) :=
  ⟨16*W+i.val, by rw [width_eq]; exact Nat.add_lt_add_left i.isLt _⟩

/-- Each retained comparator bit refers to the sending site in its physical XOR exchange. -/
def comparisonSlot (v : Word d) (i : Fin (comparisonSize d e W)) : Option (SortEdge d e W) :=
  match (offset d (2^e) W).symm (incidentIndex i) with
  | .inl _ => none
  | .inr (l,dir,j) => some (.inr (l,if dir = 0 then v else l.partner v,j))

private theorem comparison_at (f : SortEdge d e W → Bool) (v : Word d) (i : Fin (comparisonSize d e W)) :
    (comparisonSlot v i).elim false f = incidentBits (embedFields (sortEquiv f)) v (incidentIndex i) := by
  generalize hk : (offset d (2^e) W).symm (incidentIndex i) = k
  have he : offset d (2^e) W k = incidentIndex i := by rw [← hk,Equiv.apply_symm_apply]
  unfold comparisonSlot
  rw [hk,← he,incidentBits_offset]
  rcases k with ⟨dir,j⟩ | ⟨l,dir,j⟩
  · have hval := congrArg Fin.val he
    rw [offset_successor] at hval
    change 8*W*dir.val+j.val = 16*W+i.val at hval
    have hj := j.isLt
    fin_cases dir <;> simp only [Nat.mul_zero,Nat.mul_one] at hval <;> omega
  · fin_cases dir
    · exact (incident_send (embedFields (sortEquiv f)) (.inr (l,v,j))).symm
    · exact (incident_receive_sort (embedFields (sortEquiv f)) l v j).symm

private theorem comparisons_read (f : SortEdge d e W → Bool) (v : Word d) :
    List.ofFn (fun i => (comparisonSlot v i).elim false f) = comparisonBits (sortEquiv f) v := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    have hi' : i < comparisonSize d e W := by simpa using hi
    simp only [List.getElem_ofFn,comparisonBits,List.getElem_drop]
    exact comparison_at f v ⟨i,hi'⟩

/-- Literal slot names for one virtual bank in exactly the order read by the physical
sorter, including the predecessor and successor record fields. -/
def sortSlots (v : Word d) : List (Option (SortEdge d e W)) :=
  List.ofFn (boundarySlot true v) ++ (List.ofFn (boundarySlot false v) ++ List.ofFn (comparisonSlot v))

/-- Real boundary fields and raw comparator messages are recovered from one assignment
of the actual physical wires. -/
theorem sortSlots_read (f : SortEdge d e W → Bool) (v : Word d) :
    (sortSlots v).map (fun k => k.elim false f) = rowBits (sortEquiv f) v := by
  simp only [sortSlots,List.map_append,List.map_ofFn,Function.comp_def,rowBits]
  rw [boundary_read f true v,boundary_read f false v,comparisons_read]
  rfl

@[simp] theorem sortSlots_length (v : Word d) :
    (sortSlots v : List (Option (SortEdge d e W))).length = 10*W+comparisonSize d e W := by
  simp [sortSlots]; omega

end TeamContraction.Wires

end BorderVNP
end Computability
end OAI
