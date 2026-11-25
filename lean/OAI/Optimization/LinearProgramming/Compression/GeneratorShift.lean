import OAI.Optimization.LinearProgramming.Compression.GeneratorMove
import OAI.Optimization.LinearProgramming.Compression.ServiceGeneratorTable
import OAI.Optimization.LinearProgramming.RAM.StrideCopy

/-! ## Opening and filling the insertion slot of the persistent generator table -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

private theorem slot_add (n a b : ℕ) : slotBase n (a+b)=slotBase n a+b*stride n := by
  simp [slotBase,Nat.add_mul,Nat.add_assoc]

private theorem slot_succ (n a : ℕ) : slotBase n (a+1)=slotBase n a+stride n := by simp [slot_add]

private theorem slot_le {n a b : ℕ} (h : a ≤ b) : slotBase n a ≤ slotBase n b :=
  Nat.add_le_add_left (Nat.mul_le_mul_right (stride n) h) _

private theorem slot_ge (n a : ℕ) : 7 ≤ slotBase n a := by unfold slotBase tableBase; omega

/-- Postcondition for opening one empty slot. The frame includes the incoming record at
`g+1`, every preceding slot, the original input block and all preserved registers. -/
structure Shifted {K : Type*} (n pos g : ℕ) (s t : Memory K) : Prop where
  rows : ∀ i, pos ≤ i → i < g → ∀ j<stride n,
    t.data (slotBase n (i+1)+j)=s.data (slotBase n i+j)
  frame : ∀ a, a≠0 → (a<slotBase n (pos+1) ∨ slotBase n (g+1)≤a) → t.data a=s.data a
  source : t.index 8=slotBase n pos
  dest : t.index 9=slotBase n (pos+1)
  indices : ∀ i, i≠8 → i≠9 → t.index i=s.index i

/-- Move the old slots `pos,...,g-1` to `pos+1,...,g`. -/
theorem shiftSlots_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (n pos g : ℕ) (hp : pos≤g)
    (h8 : s.index 8=slotBase n g) (h9 : s.index 9=slotBase n (g+1))
    (h10 : s.index 10=slotBase n pos) (hs : s.AllData P) :
    ∃ t, Block.Eval (Memory.AllData P) moveRight s (6*((g-pos)*stride n)+1) t ∧
      Shifted n pos g s t := by
  have len (x : ℕ) (hx : pos≤x) : slotBase n pos+(x-pos)*stride n=slotBase n x := by
    rw [← slot_add]; congr 1; omega
  have len' : slotBase n pos+stride n+(g-pos)*stride n=slotBase n (g+1) := by
    rw [slot_succ,←len g hp]; omega
  obtain ⟨t,run,ts,td,copy,frame,index⟩ := moveRight_spec P s (slotBase n pos) (stride n)
    ((g-pos)*stride n) (by have := slot_ge n pos; omega) (by unfold stride; omega)
    (by rw [len g hp]; exact h8) (by rw [len']; exact h9) h10 hs
  refine ⟨t,run,?_,?_,ts,by simpa only [slot_succ] using td,index⟩
  · intro i low high j hj
    have hi : i-pos+1≤g-pos := by omega
    have mul := Nat.mul_le_mul_right (stride n) hi
    rw [Nat.add_mul,one_mul] at mul
    have copy' := copy ((i-pos)*stride n+j) (by omega)
    rw [slot_succ,← len i low]
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using copy'
  · intro a ha hf
    apply frame a ha
    simpa only [slot_succ,len'] using hf

variable {d e n pos g : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
  {q : NonzeroPairMinor D E} {s t : Memory ℚ}

/-- A shifted generator still carries its complete descriptor and actual minor magnitude. -/
theorem Shifted.slot (h : Shifted n pos g s t) {i : ℕ} (hlo : pos ≤ i) (hhi : i < g)
    (old : SlotAt D E q (slotBase n i) s) : SlotAt D E q (slotBase n (i+1)) t :=
  old.transfer (h.rows i hlo hhi)

/-- Every slot before the insertion point survives, as does the slot at the insertion point. -/
theorem Shifted.prefix (h : Shifted n pos g s t) {i : ℕ} (hi : i ≤ pos)
    (old : SlotAt D E q (slotBase n i) s) : SlotAt D E q (slotBase n i) t := by
  apply old.transfer
  intro j hj
  have hg := slot_ge n i
  have hnext : slotBase n i+stride n≤slotBase n (pos+1) := by
    rw [←slot_succ]; exact slot_le (by omega)
  exact h.frame _ (by omega) (Or.inl (by omega))

/-- The incoming request is held just beyond the shifted window. -/
theorem Shifted.incoming (h : Shifted n pos g s t)
    (old : SlotAt D E q (slotBase n (g+1)) s) : SlotAt D E q (slotBase n (g+1)) t := by
  apply old.transfer
  intro j _
  have hg := slot_ge n (g+1)
  exact h.frame _ (by omega) (Or.inr (by omega))

theorem Shifted.matrix {K : Type*} {s t : Memory K} (h : Shifted n pos g s t)
    (a : ℕ) (ha : 7≤a) (hm : a<tableBase n) : t.data a=s.data a := by
  apply h.frame a (by omega) (Or.inl ?_)
  unfold slotBase; omega

/-- Forward gather of the incoming record. Address 8 is its first scalar, 9 the first
scalar of the gap, 11 the word count; 10 is the local counter and 0 is scalar scratch. -/
def copyIncoming : Block := StrideCopy.block false 8 9 10 11 0 1 1

structure Filled {K : Type*} (n pos g : ℕ) (s t : Memory K) : Prop where
  row : ∀ j<stride n, t.data (slotBase n pos+j)=s.data (slotBase n (g+1)+j)
  frame : ∀ a, a≠0 → (a<slotBase n pos ∨ slotBase n (pos+1)≤a) → t.data a=s.data a
  source : t.index 8=slotBase n (g+2)
  dest : t.index 9=slotBase n (pos+1)
  counter : t.index 10=stride n
  indices : ∀ i, i≠8 → i≠9 → i≠10 → t.index i=s.index i

/-- Fill the hole with the request preloaded at slot `g+1`. -/
theorem copyIncoming_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (entry : Memory K) (n pos g : ℕ) (hp : pos≤g)
    (h8 : entry.index 8=slotBase n (g+1)) (h9 : entry.index 9=slotBase n pos)
    (h11 : entry.index 11=stride n) (hs : entry.AllData P) :
    ∃ t, Block.Eval (Memory.AllData P) copyIncoming entry (7*stride n+2) t ∧ Filled n pos g entry t := by
  have hgap : slotBase n pos ≤ slotBase n (g+1) := slot_le (by omega)
  have hsp := slot_ge n (g+1)
  have hdp := slot_ge n pos
  obtain ⟨t,run,row,frame,src,dst,cnt,idx⟩ := StrideCopy.block_correct P entry false
    8 9 10 11 0 1 1 (stride n) hs h11 (by decide) (by decide) (by simp)
    (by intro j hj; simp only [StrideCopy.address,StrideCopy.move,Bool.false_eq_true,ite_false,one_mul,h8]; omega)
    (by intro j hj; simp only [StrideCopy.address,StrideCopy.move,Bool.false_eq_true,ite_false,one_mul,h9]; omega)
    (by intro a j ha _; simp only [StrideCopy.address,StrideCopy.move,Bool.false_eq_true,ite_false,one_mul,h8,h9]; omega)
  simp only [StrideCopy.address,StrideCopy.move,Bool.false_eq_true,ite_false,one_mul,h8,h9] at row frame src dst
  refine ⟨t,?_,row,?_,?_,?_,cnt,idx⟩
  · simpa only [copyIncoming,show 1+1+5=7 by decide,Nat.mul_comm 7] using run
  · intro a ha hf
    apply frame a ha
    intro j hj
    rw [slot_succ] at hf
    omega
  · simpa only [show g+2=(g+1)+1 by omega,slot_succ n (g+1)] using src
  · simpa only [slot_succ] using dst

theorem Filled.slot (h : Filled n pos g s t)
    (old : SlotAt D E q (slotBase n (g+1)) s) : SlotAt D E q (slotBase n pos) t := old.transfer h.row

theorem Filled.other (h : Filled n pos g s t) {i : ℕ} (hi : i≠pos)
    (old : SlotAt D E q (slotBase n i) s) : SlotAt D E q (slotBase n i) t := by
  apply old.transfer
  intro j hj
  have hg := slot_ge n i
  apply h.frame _ (by omega)
  rcases lt_or_gt_of_ne hi with hlo | hhi
  · have x : slotBase n (i+1)≤slotBase n pos := slot_le hlo
    rw [slot_succ] at x; omega
  · have x : slotBase n (pos+1)≤slotBase n i := slot_le hhi
    omega

theorem Filled.matrix {K : Type*} {s t : Memory K} (h : Filled n pos g s t)
    (a : ℕ) (ha : 7≤a) (hm : a<tableBase n) : t.data a=s.data a := by
  apply h.frame a (by omega) (Or.inl ?_)
  unfold slotBase; omega

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
