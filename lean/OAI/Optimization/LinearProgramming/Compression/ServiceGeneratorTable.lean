import OAI.Optimization.LinearProgramming.Compression.MinorOrder
import OAI.Optimization.LinearProgramming.Compression.MinorLoadInput
import Mathlib.Data.Finset.Sort

/-! Scalar-resident generator records for the online minor service. Every row preserves its
matrix selector and both sorted index lists, including order zero. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

variable {d e n : ℕ}

/-- The table starts immediately after the two original scalar matrices. -/
def tableBase (n : ℕ) := 7+n*n

def stride (n : ℕ) := 2*n+3

def slotBase (n a : ℕ) := tableBase n+a*stride n

def tag : PairMinorIndex d e n → ℕ
  | .inl _ => 0
  | .inr _ => 1

def order : PairMinorIndex d e n → ℕ
  | .inl u => u.1.val
  | .inr u => u.1.val

def rowWord : PairMinorIndex d e n → ℕ → ℕ
  | .inl u, i => if h : i < u.1.val then (u.2.1 ⟨i,h⟩).val else 0
  | .inr u, i => if h : i < u.1.val then (u.2.1 ⟨i,h⟩).val else 0

def colWord : PairMinorIndex d e n → ℕ → ℕ
  | .inl u, i => if h : i < u.1.val then (u.2.2 ⟨i,h⟩).val else 0
  | .inr u, i => if h : i < u.1.val then (u.2.2 ⟨i,h⟩).val else 0

theorem order_le (u : PairMinorIndex d e n) : order u ≤ n := by
  rcases u with ⟨k,r,c⟩ | ⟨k,r,c⟩ <;> exact Nat.le_of_lt_succ k.isLt

theorem rowWord_le (u : PairMinorIndex d e n) (h : d+e=n) (i : ℕ) : rowWord u i ≤ n := by
  rcases u with u | u <;> simp only [rowWord] <;> split
  · exact (u.2.1 _).isLt.le.trans (by omega)
  · exact Nat.zero_le _
  · exact (u.2.1 _).isLt.le.trans (by omega)
  · exact Nat.zero_le _

theorem colWord_le (u : PairMinorIndex d e n) (i : ℕ) : colWord u i ≤ n := by
  rcases u with u | u <;> simp only [colWord] <;> split
  · exact (u.2.2 _).isLt.le
  · exact Nat.zero_le _
  · exact (u.2.2 _).isLt.le
  · exact Nat.zero_le _

/-- The interleaved comparison keys used by the model and the native slot scanner agree. -/
theorem pairMinorKey_words (u : PairMinorIndex d e n) : pairMinorKey u =
    tag u :: order u :: List.ofFn (fun i : Fin (order u) => Nat.pair (rowWord u i.val) (colWord u i.val)) := by
  rcases u with ⟨k,r,c⟩ | ⟨k,r,c⟩
  · change 0 :: k.val :: List.ofFn (fun i => Nat.pair (r i).val (c i).val) = _
    simp [tag,order,rowWord,colWord]
  · change 1 :: k.val :: List.ofFn (fun i => Nat.pair (r i).val (c i).val) = _
    simp [tag,order,rowWord,colWord]

/-- One padded generator row, ending with the positive magnitude of its actual nonzero minor. -/
structure SlotAt (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (u : NonzeroPairMinor D E) (base : ℕ) (s : Memory ℚ) : Prop where
  tag : s.data base = (GeneratorTable.tag u.val : ℚ)
  order : s.data (base+1) = (GeneratorTable.order u.val : ℚ)
  rows : ∀ i : Fin n, s.data (base+2+i.val) = (rowWord u.val i.val : ℚ)
  cols : ∀ i : Fin n, s.data (base+2+n+i.val) = (colWord u.val i.val : ℚ)
  magnitude : s.data (base+2+2*n) = |pairMinorValue D E u.val|

/-- Transferring all scalars in a row preserves the descriptor and magnitude together. -/
theorem SlotAt.transfer {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
    {u : NonzeroPairMinor D E} {a b : ℕ} {s t : Memory ℚ} (h : SlotAt D E u a s)
    (copy : ∀ j < stride n, t.data (b+j)=s.data (a+j)) : SlotAt D E u b t := by
  refine ⟨?_,(copy 1 (by unfold stride; omega)).trans h.order,?_,?_,?_⟩
  · simpa using (copy 0 (by unfold stride; omega)).trans (by simpa using h.tag)
  · intro i
    have hi := i.isLt
    simpa [Nat.add_assoc] using (copy (2+i.val) (by unfold stride; omega)).trans (by simpa [Nat.add_assoc] using h.rows i)
  · intro i
    have hi := i.isLt
    simpa [Nat.add_assoc] using (copy (2+n+i.val) (by unfold stride; omega)).trans (by simpa [Nat.add_assoc] using h.cols i)
  · simpa [Nat.add_assoc] using (copy (2+2*n) (by unfold stride; omega)).trans (by simpa [Nat.add_assoc] using h.magnitude)

/-- A sorted list and a bounded scalar table describe exactly the same generators. -/
structure Stored (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (keys : List (NonzeroPairMinor D E)) (s : Memory ℚ) : Prop where
  sorted : keys.Pairwise (· < ·)
  count : s.data 4 = (keys.length : ℚ)
  slots : ∀ i : Fin keys.length, SlotAt D E keys[i.val] (slotBase n i.val) s

theorem Stored.empty (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (s : Memory ℚ) (hc : s.data 4 = 0) : Stored D E [] s := ⟨.nil, by simpa using hc, fun i => Fin.elim0 i⟩

/-- Native comparison contract: physical slot addresses in 20/21, dimension in 22,
result (<, =, >) in 23. The comparison leaves the two scalar rows untouched. -/
def SlotComparatorSpec (b : Block) (C : ℕ → ℕ) : Prop :=
  ∀ {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (y q : NonzeroPairMinor D E) (P : ℚ → Prop) (s : Memory ℚ),
    d+e=n → s.index 22=n → SlotAt D E y (s.index 20) s → SlotAt D E q (s.index 21) s →
    7≤s.index 20 → 7≤s.index 21 → (∀ a, P (s.data a)) → (∀ j≤4*(n+1)^2, P (j : ℚ)) →
    ∃ t k, k≤C n ∧ Block.Eval (fun z => ∀ a, P (z.data a)) b s k t ∧
      t.index 23 = (if y<q then 0 else if y=q then 1 else 2) ∧
      (∀ a, a<23 ∨ 40≤a → t.index a=s.index a) ∧
      (∀ a, a≠0 → a≠5 → a≠6 → t.data a=s.data a)

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
