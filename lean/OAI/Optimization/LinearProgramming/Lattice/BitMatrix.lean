import OAI.Optimization.LinearProgramming.Lattice.BitState
import OAI.Optimization.LinearProgramming.Lattice.BitList
import OAI.Computability.QuantumFactoring.BitStackIntegers

/-! Row primitives for the packed integral LLL state. Every read, update and signed
integer operation is a finite Boolean-stack procedure with a verified polynomial clock. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- The framed matrix is indexed by binary row numbers and uses an empty default row. -/
noncomputable def rowReadP : Procedure (prodCode Nat.bits intMatrixCode) intRowCode
    (fun z => rowAt z.2 z.1) := listGet intRowCode []

noncomputable def rowSetP : Procedure (prodCode (prodCode Nat.bits intRowCode) intMatrixCode) intMatrixCode
    (fun z => z.2.set z.1.1 z.1.2) := setNthP intRowCode []

theorem readAt_eq_getElem {α : Type} (d : α) (xs : List α) (i : ℕ) (hi : i<xs.length) :
    readAt d xs i = xs[i] := by simp [readAt, List.getElem?_eq_getElem hi]

theorem readAt_set {α : Type} (d x : α) (xs : List α) (i j : ℕ) :
    readAt d (xs.set i x) j = if i=j ∧ i<xs.length then x else readAt d xs j := by
  by_cases hij : i=j
  · subst j
    by_cases hi : i<xs.length
    · simp [readAt,hi]
    · simp [List.set_eq_of_length_le (Nat.le_of_not_gt hi),hi]
  · simp [readAt,hij]

/-- Replacing an in-range entry exchanges exactly the two encoded element lengths.
List framing doubles each payload length. -/
theorem listCode_length_set_exact {α : Type} (e : α → List Bool) (xs : List α) (i : ℕ)
    (x : α) (hi : i<xs.length) :
    (listCode e (xs.set i x)).length + 2*(e xs[i]).length =
      (listCode e xs).length + 2*(e x).length := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons y ys ih =>
    cases i with
    | zero => simp only [List.set_cons_zero,List.getElem_cons_zero,listCode_length_cons]; omega
    | succ i =>
      have h : i<ys.length := by simpa using hi
      have hrec := ih i h
      simp only [List.set_cons_succ,List.getElem_cons_succ,listCode_length_cons]
      omega

theorem listCode_length_set_le {α : Type} (e : α → List Bool) (xs : List α) (i : ℕ) (x : α) :
    (listCode e (xs.set i x)).length ≤ (listCode e xs).length + 2*(e x).length := by
  by_cases hi : i<xs.length
  · have := listCode_length_set_exact e xs i x hi; omega
  · rw [List.set_eq_of_length_le (Nat.le_of_not_gt hi)]; omega

/-- Exchange valid rows. A malformed pair of indices leaves the matrix unchanged. -/
def swapRows (i j : ℕ) (A : IntMatrix) : IntMatrix :=
  if i<A.length ∧ j<A.length then (A.set i (rowAt A j)).set j (rowAt A i) else A

noncomputable def swapRowsP : Procedure (prodCode (prodCode Nat.bits Nat.bits) intMatrixCode)
    intMatrixCode (fun z => swapRows z.1.1 z.1.2 z.2) := by
  let indices := first (prodCode Nat.bits Nat.bits) intMatrixCode
  let rows := second (prodCode Nat.bits Nat.bits) intMatrixCode
  let i := (first Nat.bits Nat.bits).comp indices
  let j := (second Nat.bits Nat.bits).comp indices
  let a := rowReadP.comp (i.pair rows)
  let b := rowReadP.comp (j.pair rows)
  let left := rowSetP.comp ((i.pair b).pair rows)
  let both := rowSetP.comp ((j.pair a).pair left)
  let n := (listLength intRowCode []).comp rows
  let valid := boolAnd.comp ((binaryLt.comp (i.pair n)).pair (binaryLt.comp (j.pair n)))
  exact (conditional valid both rows).congrFun (by
    rintro ⟨⟨i,j⟩,A⟩
    change (if decide (i<A.length) && decide (j<A.length) then _ else _) = _
    by_cases hi : i<A.length <;> by_cases hj : j<A.length <;> simp [swapRows,hi,hj])

@[simp] theorem length_swapRows (i j : ℕ) (A : IntMatrix) : (swapRows i j A).length = A.length := by
  unfold swapRows
  split <;> simp

theorem rowAt_swapRows {A : IntMatrix} {i j : ℕ} (hi : i<A.length) (hj : j<A.length) (k : ℕ) :
    rowAt (swapRows i j A) k = if k=i then rowAt A j else if k=j then rowAt A i else rowAt A k := by
  unfold swapRows
  simp only [hi,hj,and_self,ite_true]
  change readAt _ _ _ = _
  rw [readAt_set,readAt_set]
  by_cases hki : k=i <;> by_cases hkj : k=j <;> simp_all [rowAt,eq_comm]

/-- Row swaps preserve the complete matrix bit length, not only the number of rows. -/
@[simp] theorem intMatrixCode_length_swapRows (i j : ℕ) (A : IntMatrix) :
    (intMatrixCode (swapRows i j A)).length = (intMatrixCode A).length := by
  unfold swapRows
  split
  · rename_i h
    obtain ⟨hi,hj⟩ := h
    have e₁ := listCode_length_set_exact intRowCode A i (rowAt A j) hi
    have e₂ := listCode_length_set_exact intRowCode (A.set i (rowAt A j)) j (rowAt A i)
      (by simpa using hj)
    have aj : (A.set i (rowAt A j))[j]'(by simpa using hj) = rowAt A j := by
      rw [List.getElem_set]
      split
      · rfl
      · exact (readAt_eq_getElem [] A j hj).symm
    rw [aj] at e₂
    have ai : A[i] = rowAt A i := (readAt_eq_getElem [] A i hi).symm
    rw [ai] at e₁
    unfold intMatrixCode
    omega
  · rfl

/-- Coordinatewise `target - r * source` retains every target coordinate and treats
a missing source coordinate as zero. -/
def subMulRow (r : ℤ) (target source : List ℤ) : List ℤ :=
  target.mapIdx fun i t => t-r*readAt 0 source i

noncomputable def subMulRowP :
    Procedure (prodCode (prodCode intCode intRowCode) intRowCode) intRowCode
      (fun z => subMulRow z.1.1 z.1.2 z.2) := by
  let env := prodCode (prodCode intCode intRowCode) intRowCode
  let slot := second unaryCode env
  let pair := first (prodCode intCode intRowCode) intRowCode
  let r := (first intCode intRowCode).comp (pair.comp slot)
  let target := (second intCode intRowCode).comp pair
  let source := second (prodCode intCode intRowCode) intRowCode
  let i := unaryToBits.comp (first unaryCode env)
  let a := (listGet intCode 0).comp (i.pair (target.comp slot))
  let b := (listGet intCode 0).comp (i.pair (source.comp slot))
  let op := intSub.comp (a.pair (intMul.comp (r.pair b)))
  let f := fun (z : (ℤ × List ℤ) × List ℤ) (k : ℕ) =>
    readAt 0 z.1.2 k-z.1.1*readAt 0 z.2 k
  have entry : Procedure (prodCode unaryCode env) intCode (fun z => f z.2 z.1) := op
  exact (tabulateAlongP (ea:=intCode) (eb:=intCode) 0 0 target entry).congrFun (by
    rintro ⟨⟨r,ts⟩,ss⟩
    change (List.range ts.length).map (fun i => readAt 0 ts i-r*readAt 0 ss i) = subMulRow r ts ss
    apply List.ext_getElem
    · simp [subMulRow]
    · intro j _ hj
      have h : j<ts.length := by simpa [subMulRow] using hj
      simp [subMulRow,readAt_eq_getElem 0 ts j h])

@[simp] theorem length_subMulRow (r : ℤ) (target source : List ℤ) :
    (subMulRow r target source).length = target.length := by simp [subMulRow]

theorem readAt_subMulRow (r : ℤ) (target source : List ℤ) {i : ℕ} (hi : i<target.length) :
    readAt 0 (subMulRow r target source) i = readAt 0 target i-r*readAt 0 source i := by
  rw [readAt_eq_getElem _ _ i (by simpa using hi),readAt_eq_getElem _ target i hi]
  simp [subMulRow]

/-- Each output entry is bounded by one integer multiplication and one subtraction.
This accounts for arbitrary input magnitudes, including signs and short source rows. -/
theorem natAbs_readAt_subMulRow (r : ℤ) (target source : List ℤ) {i : ℕ} (hi : i<target.length) :
    (readAt 0 (subMulRow r target source) i).natAbs ≤
      (readAt 0 target i).natAbs + r.natAbs*(readAt 0 source i).natAbs := by
  rw [readAt_subMulRow r target source hi]
  simpa [sub_eq_add_neg,Int.natAbs_mul] using
    Int.natAbs_add_le (readAt 0 target i) (-(r*readAt 0 source i))

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
