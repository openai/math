import OAI.Hierarchy.DescentRetainedRangeDigits
import OAI.Hierarchy.DescentOperandWidth

namespace OAI
/-! # The actual range digits fit the scheduled operand word -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentBundleHistory DescentKernelHistory DescentSixParty DescentCompiler
noncomputable section
variable {p : ℕ} {U V : Type} {w : V→ℕ} {r : BitRecipe U V w}

theorem occurrence_bound (s : Shape p r) (u : r.Node) (drift : ℕ)
    (bound : ∀ (j : Fin (r.arity u)) (g : Fin (s.groups u j)), (s.chunk u j g).stride≤drift)
    (q : SliceCode) (member_ : q∈occurrences s u) :
    q.start<p ∧ q.stride≤drift ∧ q.count≤drift+1 := by
  unfold occurrences at member_
  obtain ⟨row,rowIn,within⟩:=List.mem_flatMap.mp member_
  unfold Shape.rows at rowIn
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp rowIn
  obtain ⟨t,here,located⟩:=List.mem_flatMap.mp within
  obtain ⟨g,rfl⟩:=List.mem_ofFn.mp here
  have found : q = (s.chunk u j g).code := (List.mem_replicate.mp located).2
  rw [found]
  exact ⟨(s.chunk u j g).residue,bound j g,(s.chunk u j g).bound.trans (Nat.succ_le_succ (bound j g))⟩

variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)
theorem atSlot_fits (s : Shape p r) (u : r.Node) (k tail drift degree : ℕ)
    (bound : ∀ (j : Fin (r.arity u)) (g : Fin (s.groups u j)), (s.chunk u j g).stride≤drift)
    (slot : ℕ) (f : Fin 3) :
    atSlot s u slot f<2^(DescentOperandWidth.recordBits G S k tail drift degree p) := by
  cases found : (occurrences s u)[slot]? with
  | none=>simpa only [atSlot,found,Option.elim_none] using Nat.two_pow_pos (DescentOperandWidth.recordBits G S k tail drift degree p)
  | some q=>
    have mem : q∈occurrences s u := List.mem_of_getElem? found
    obtain ⟨start,stride,last⟩:=occurrence_bound s u drift bound q mem
    simp only [atSlot,found,Option.elim_some]
    fin_cases f
    · exact DescentOperandWidth.bitOffset G S start.le
    · exact DescentOperandWidth.runLength G S (stride.trans (Nat.le_succ _))
    · exact DescentOperandWidth.runLength G S last

open scoped Fin.CommRing in
theorem stored_atSlot {b : ℕ} (s : Shape p r) (u : r.Node) (k tail drift degree : ℕ)
    (bound : ∀ (j : Fin (r.arity u)) (g : Fin (s.groups u j)), (s.chunk u j g).stride≤drift)
    (slot : ℕ) (f : Fin 3)
    (printed : DescentSIMDLookup.Cell b) (correct : printed.val=atSlot s u slot f) :
    ((printed.val:DescentSIMDLookup.Cell (DescentOperandWidth.recordBits G S k tail drift degree p))).val =
      atSlot s u slot f := by
  rw [correct,Fin.val_cast_of_lt (atSlot_fits G S s u k tail drift degree bound slot f)]

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
