import OAI.Optimization.LinearProgramming.Compression.CircuitMachine
import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
import Mathlib.Tactic

/-! Arithmetic circuits for the division-free Bird determinant recurrence. At each stage
all matrix entries read only the input and the preceding stored matrix. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- The left inputs name cells in the original matrix and the right inputs name cells
in the previous Bird iterate. -/
abbrev BirdRead (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

def sumExpr {ι : Type} : (k : ℕ) → (Fin k → ArithExpr ι) → ArithExpr ι
  | 0, _ => .zero
  | k + 1, f => .add (f 0) (sumExpr k fun i => f i.succ)

theorem eval_sumExpr {ι K : Type} [CommRing K] (v : ι → K) (k : ℕ) (f : Fin k → ArithExpr ι) :
    (sumExpr k f).eval v = ∑ i, (f i).eval v := by
  induction k with
  | zero => simp [sumExpr, ArithExpr.eval]
  | succ k ih => simp [sumExpr, ArithExpr.eval, ih, Fin.sum_univ_succ]

theorem size_sumExpr {ι : Type} (k C : ℕ) (f : Fin k → ArithExpr ι)
    (h : ∀ i, (f i).size ≤ C) : (sumExpr k f).size ≤ 1 + k * (C + 1) := by
  induction k with
  | zero => simp [sumExpr, ArithExpr.size]
  | succ k ih =>
    have hfirst := h 0
    have hprev := ih (fun i => f i.succ) (fun i => h i.succ)
    simp only [sumExpr, ArithExpr.size, Nat.succ_mul]
    omega

/-- A single output cell at a single stage of the determinant calculation. -/
def birdStepExpr {n : ℕ} (i j : Fin n) : ArithExpr (BirdRead n) :=
  let diagonal := sumExpr n fun k =>
    if i < k then .read (.inr (k, k)) else .zero
  let products := sumExpr n fun k =>
    if i < k then .mul (.read (.inr (i, k))) (.read (.inl (k, j))) else .zero
  .add (.mul (.neg diagonal) (.read (.inl (i, j)))) products

def readBird {K : Type} {n : ℕ} (A F : Matrix (Fin n) (Fin n) K) : BirdRead n → K :=
  Sum.elim (fun ij => A ij.1 ij.2) (fun ij => F ij.1 ij.2)

private theorem eval_iteExpr {ι K : Type} [Ring K] (v : ι → K) (p : Prop) [Decidable p]
    (a b : ArithExpr ι) : (if p then a else b).eval v = if p then a.eval v else b.eval v := by
  split <;> rfl

theorem eval_birdStepExpr {K : Type} [CommRing K] {n : ℕ}
    (A F : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (birdStepExpr i j).eval (readBird A F) = BirdDet.Spec.stepEntry A F i j := by
  simp [birdStepExpr, ArithExpr.eval, eval_sumExpr, readBird, BirdDet.Spec.stepEntry_eq,
    eval_iteExpr, ← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

theorem size_birdStepExpr {n : ℕ} (i j : Fin n) : (birdStepExpr i j).size ≤ 6 * (n + 1) := by
  have hd := size_sumExpr (ι := BirdRead n) n 1
    (fun k => if i < k then .read (.inr (k, k)) else .zero) (by
      intro k; split <;> simp [ArithExpr.size])
  have hp := size_sumExpr (ι := BirdRead n) n 3
    (fun k => if i < k then .mul (.read (.inr (i, k))) (.read (.inl (k, j))) else .zero) (by
      intro k; split <;> simp [ArithExpr.size])
  simp only [birdStepExpr, ArithExpr.size]
  omega

/-- Evaluate one complete stage from one stored input matrix and one stored previous stage. -/
def birdStage {K : Type} [CommRing K] {n : ℕ} (A F : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K := .of fun i j => (birdStepExpr i j).eval (readBird A F)

theorem birdStage_eq {K : Type} [CommRing K] {n : ℕ} (A F : Matrix (Fin n) (Fin n) K) :
    birdStage A F = BirdDet.Spec.stepEntry A F := by
  ext i j
  exact eval_birdStepExpr A F i j

private theorem sumFrom_fin {K : Type} [CommRing K] {n : ℕ} (i : Fin n) (f : ℕ → K) :
    BirdDet.sumFrom n (i.val + 1) f = ∑ k ∈ Finset.Ioi i, f k.val := by
  have hsum (lo : ℕ) : BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
    induction lo using BirdDet.sumFrom_induct n with
    | step lo hlo ih => rw [BirdDet.sumFrom_step _ _ _ hlo, ih, Finset.sum_eq_sum_Ico_succ_bot hlo f]
    | stop lo hlo => rw [BirdDet.sumFrom_stop _ _ _ hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]
  rw [hsum]
  calc
    _ = ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by congr; ext; aesop
    _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
    _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by rw [← Fin.sum_univ_eq_sum_range]
    _ = _ := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

private theorem arrayIter_eq {K : Type} [CommRing K] {n : ℕ} (A : Array K) (hA : A.size = n*n)
    (t : ℕ) (i j : Fin n) :
    ((BirdDet.stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val =
      (BirdDet.Spec.stepEntry (Matrix.ofArray A hA))^[t] (Matrix.ofArray A hA) i j := by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [BirdDet.get_eq]
  | succ t ih =>
    simp_rw [Function.iterate_succ_apply', BirdDet.stepEntry_eq, BirdDet.Spec.stepEntry_eq,
      sumFrom_fin, ih, Matrix.of_apply, BirdDet.get_eq]

/-- One pass through the `k` stages computes the determinant of a `(k+1) × (k+1)` matrix. -/
theorem det_from_birdStages {K : Type} [CommRing K] {k : ℕ}
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    A.det = (-1 : K)^k * ((birdStage A)^[k] A) 0 0 := by
  let a : Array K := Array.ofFn fun i : Fin ((k+1)*(k+1)) => A i.divNat i.modNat
  have ha : a.size = (k+1)*(k+1) := by simp [a]
  have hm : Matrix.ofArray a ha = A := Matrix.ofArray_ofFn A
  have h := BirdDet.det_eq_birdDet a ha
  rw [hm, BirdDet.birdDet_succ] at h
  have he := arrayIter_eq a ha k (0 : Fin (k+1)) (0 : Fin (k+1))
  rw [hm] at he
  rw [show birdStage A = BirdDet.Spec.stepEntry A from funext (birdStage_eq A)]
  simpa only [Fin.val_zero] using h.trans (congrArg ((-1 : K)^k * ·) he)

/-- The sum counts each expression node once per output cell per stage. -/
def birdStageNodes (n : ℕ) : ℕ := ∑ i : Fin n, ∑ j : Fin n, (birdStepExpr i j).size

theorem birdStageNodes_le (n : ℕ) : birdStageNodes n ≤ n^2 * (6 * (n+1)) := by
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, 6 * (n+1) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => size_birdStepExpr i j
    _ = _ := by simp [pow_two, Nat.mul_assoc]

/-- The total node count is quartic in the dimension, including a final sign correction. -/
theorem birdDet_nodes_le (n : ℕ) :
    (n-1) * birdStageNodes n + 2 ≤ 8 * (n+1)^4 := by
  have h := Nat.mul_le_mul (Nat.sub_le n 1) (birdStageNodes_le n)
  nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^2)]

end Compression
end LinearProgramming
end Optimization
end OAI
