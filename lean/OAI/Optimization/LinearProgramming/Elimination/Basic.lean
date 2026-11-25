import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.List.FinRange

/-! Exact row and column bases and linear solves over an ordered field. A single scan tests
independence by a Gram determinant. Bird's determinant recurrence is tabulated at every stage.
The dimension trace records each determinant query in the scan. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open Matrix Module Submodule
open scoped Matrix BigOperators

variable {K : Type*} {m d r : ℕ}

/-- Materialize all entries before the next determinant stage reuses them. -/
def tabulate [Zero K] (A : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin r) K :=
  Matrix.ofArray (Array.ofFn fun j : Fin (r*r) => A j.divNat j.modNat) (by simp)

@[simp] theorem tabulate_eq [Zero K] (A : Matrix (Fin r) (Fin r) K) : tabulate A = A :=
  Matrix.ofArray_ofFn A

/-- Cache every in-bounds entry of the Bird recurrence. Its total extension on out-of-range
indices permits direct comparison with Mathlib's row-major recurrence. -/
private def cacheEntries [Zero K] (n : ℕ) (f : ℕ → ℕ → K) : ℕ → ℕ → K :=
  let t := tabulate (Matrix.of fun i j : Fin n => f i.val j.val)
  fun i j => if hi : i < n then if hj : j < n then t ⟨i, hi⟩ ⟨j, hj⟩ else f i j else f i j

private theorem cacheEntries_eq [Zero K] (n : ℕ) (f : ℕ → ℕ → K) : cacheEntries n f = f := by
  funext i j
  simp [cacheEntries]

/-- Division-free determinant with a fresh materialized table for each product stage. -/
def determinant [CommRing K] : {r : ℕ} → Matrix (Fin r) (Fin r) K → K
  | 0, _ => 1
  | k + 1, A =>
    let n := k + 1
    let a := Array.ofFn fun x : Fin (n*n) => A x.divNat x.modNat
    (-1 : K)^k * ((fun f => cacheEntries n (BirdDet.stepEntry n a f))^[k] (BirdDet.get n a)) 0 0

@[simp] theorem determinant_eq [CommRing K] (A : Matrix (Fin r) (Fin r) K) :
    determinant A = A.det := by
  cases r with
  | zero => simp [determinant]
  | succ k =>
    let a := Array.ofFn fun x : Fin ((k+1)*(k+1)) => A x.divNat x.modNat
    have ha : a.size = (k+1)*(k+1) := by simp [a]
    have heq := BirdDet.det_eq_birdDet a ha
    rw [show Matrix.ofArray a ha = A from Matrix.ofArray_ofFn A] at heq
    simpa only [determinant, cacheEntries_eq, BirdDet.birdDet_succ, a] using heq.symm

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Ordered fields have the same kernel for a rectangular matrix and its Gram matrix. -/
theorem gram_det_ne_zero (B : Matrix (Fin m) (Fin r) K) :
    determinant (Bᵀ * B) ≠ 0 ↔ LinearIndependent K B.col := by
  rw [determinant_eq, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.mulVec_injective_iff_isUnit, ← Matrix.mulVec_injective_iff]
  change Function.Injective (Bᵀ * B).mulVecLin ↔ Function.Injective B.mulVecLin
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_transpose_mul_self]

/-- Columns selected in list order. -/
def columns (A : Matrix (Fin m) (Fin d) K) (s : List (Fin d)) : Matrix (Fin m) (Fin s.length) K :=
  A.submatrix id s.get

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem columns_cons (A : Matrix (Fin m) (Fin d) K) (j : Fin d) (s : List (Fin d)) :
    (columns A (j :: s)).col = Fin.cons (A.col j) (columns A s).col := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

structure Selection (d : ℕ) where
  indices : List (Fin d)
  dimensions : List ℕ

/-- One independent-column decision per input index, including zero and repeated columns. -/
def scan (A : Matrix (Fin m) (Fin d) K) : List (Fin d) → Selection d
  | [] => ⟨[], []⟩
  | j :: js =>
    let prev := scan A js
    let cand := j :: prev.indices
    let B := columns A cand
    let idx := if determinant (Bᵀ * B) = 0 then prev.indices else cand
    ⟨idx, cand.length :: prev.dimensions⟩

private theorem scan_independent_span (A : Matrix (Fin m) (Fin d) K) (js : List (Fin d)) :
    LinearIndependent K (columns A (scan A js).indices).col ∧
    span K (Set.range (columns A (scan A js).indices).col) = span K (Set.range (columns A js).col) := by
  induction js with
  | nil =>
    change LinearIndependent K (columns A []).col ∧ _
    let : IsEmpty (Fin (([] : List (Fin d)).length)) := ⟨fun i => Fin.elim0 i⟩
    exact ⟨linearIndependent_empty_type, rfl⟩
  | cons j js ih =>
    let s := (scan A js).indices
    let B := columns A (j :: s)
    have hind : LinearIndependent K (columns A s).col := ih.1
    have hspan : span K (Set.range (columns A s).col) = span K (Set.range (columns A js).col) := ih.2
    by_cases h : determinant (Bᵀ * B) = 0
    · have hmem : A.col j ∈ span K (Set.range (columns A s).col) := by
        by_contra hmem
        apply (gram_det_ne_zero B).2 _ h
        rw [show B = columns A (j :: s) from rfl, columns_cons, linearIndependent_finCons]
        exact ⟨hind, hmem⟩
      have eqs : (scan A (j :: js)).indices = s := ite_eq_left h
      rw [eqs, columns_cons, Fin.range_cons, span_insert_eq_span (hspan ▸ hmem)]
      exact ⟨hind, hspan⟩
    · have hli := (gram_det_ne_zero B).1 h
      have eqs : (scan A (j :: js)).indices = j :: s := ite_eq_right h
      refine ⟨eqs ▸ hli, ?_⟩
      rw [eqs, columns_cons, columns_cons, Fin.range_cons, Fin.range_cons,
        span_insert, span_insert, hspan]

omit [IsStrictOrderedRing K] in
/-- The recorded determinant dimensions are all bounded by the number of input columns. -/
theorem scan_cost (A : Matrix (Fin m) (Fin d) K) (js : List (Fin d)) :
    (scan A js).indices.length ≤ js.length ∧ (scan A js).dimensions.length = js.length ∧
      ∀ k ∈ (scan A js).dimensions, k ≤ js.length := by
  induction js with
  | nil => simp [scan]
  | cons j js ih =>
    simp only [scan, List.length_cons, List.mem_cons]
    refine ⟨?_, by omega, fun k hk => ?_⟩
    · split
      · exact ih.1.trans (Nat.le_succ _)
      · simpa using ih.1
    · rcases hk with rfl | hk
      · omega
      · exact (ih.2.2 k hk).trans (Nat.le_succ _)

def columnBasis (A : Matrix (Fin m) (Fin d) K) : List (Fin d) :=
  (scan A (List.finRange d)).indices

/-- The scan returns actual input column indices, linearly independent and spanning the entire
column space. -/
theorem columnBasis_spec (A : Matrix (Fin m) (Fin d) K) :
    LinearIndependent K (columns A (columnBasis A)).col ∧
    span K (Set.range (columns A (columnBasis A)).col) = span K (Set.range A.col) := by
  obtain ⟨hi, hs⟩ := scan_independent_span A (List.finRange d)
  refine ⟨hi, hs.trans ?_⟩
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (List.mem_finRange i)
    exact ⟨j, congrArg A.col hj⟩

/-- Cardinality of the extracted basis computes matrix rank. -/
theorem columnBasis_length (A : Matrix (Fin m) (Fin d) K) : (columnBasis A).length = A.rank := by
  obtain ⟨hi, hs⟩ := columnBasis_spec A
  rw [A.rank_eq_finrank_span_cols, ← hs]
  simpa using (finrank_span_eq_card hi).symm

end Elimination
end LinearProgramming
end Optimization
end OAI
