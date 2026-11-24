import OAI.Computability.VPVNP.VerifierMachineNetwork
import Mathlib.Algebra.BigOperators.Fin

/-!
# Boolean circuit checking row counts

The coefficient oracle of §8.1 counts the selected terminal and production events.
Each event flag may increment the counts of any fixed set of rows. At each stage this
circuit maintains one bit for every row and every count from zero through the number
of flags. Its final layer compares those bits with the supplied one-hot target table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace OracleTally

open VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

/-- Flag wires followed by the row and count coordinates of the one-hot table. -/
abbrev Input (Rows : Type*) (k : ℕ) := Fin k ⊕ Rows × Fin (k + 1)

variable {Rows : Type*} {k : ℕ}

/-- Number of selected flags that are set in this row. -/
def rowCount (selected : Rows → Fin k → Bool) (x : Fin k → Bool) (r : Rows) : ℕ :=
  ∑ i, if selected r i && x i then 1 else 0

/-- The target marks exactly the attained count in each row. -/
def RowCountsOK (selected : Rows → Fin k → Bool) (x : Fin k → Bool)
    (target : Rows → Fin (k+1) → Bool) : Prop :=
  ∀ r j, target r j = decide (rowCount selected x r = j.val)

theorem rowCount_le (selected : Rows → Fin k → Bool) (x : Fin k → Bool) (r : Rows) :
    rowCount selected x r ≤ k := by
  calc
    rowCount selected x r ≤ ∑ _ : Fin k, 1 := by
      unfold rowCount
      apply Finset.sum_le_sum
      intro i _
      split <;> decide
    _ = k := by simp

/-- An all-zero target row for a count greater than `k` is rejected as well. -/
theorem rowCountsOK_oneHot_iff (selected : Rows → Fin k → Bool) (x : Fin k → Bool)
    (wanted : Rows → ℕ) :
    RowCountsOK selected x (fun r j ↦ decide (wanted r = j.val)) ↔
      ∀ r, rowCount selected x r = wanted r := by
  constructor
  · intro h r
    let j : Fin (k+1) := ⟨rowCount selected x r, Nat.lt_succ_of_le (rowCount_le _ _ _)⟩
    have hj := h r j
    simpa [j, eq_comm] using hj
  · intro h r j
    rw [h]

private def prefixCount (selected : Rows → Fin k → Bool) (x : Fin k → Bool)
    (r : Rows) (t : ℕ) : ℕ :=
  ∑ a ∈ Finset.range t, if h : a < k then
    (if selected r ⟨a,h⟩ && x ⟨a,h⟩ then 1 else 0) else 0

private theorem prefixCount_full (selected : Rows → Fin k → Bool) (x : Fin k → Bool)
    (r : Rows) : prefixCount selected x r k = rowCount selected x r :=
  (Finset.sum_fin_eq_sum_range (fun i ↦ if selected r i && x i then 1 else 0)).symm

private def initialExpr : Input Rows k → Expr (Input Rows k)
  | .inl i => .input (.inl i)
  | .inr (_, j) => .const (decide (0 = j.val))

private def previousExpr (r : Rows) (j : Fin (k+1)) : Expr (Input Rows k) :=
  if j.val = 0 then .const false
  else .input (.inr (r, ⟨j.val - 1, by have := j.isLt; omega⟩))

private def layerExpr (selected : Rows → Fin k → Bool) (t : ℕ) :
    Input Rows k → Expr (Input Rows k)
  | .inl i => .input (.inl i)
  | .inr (r, j) =>
    if ht : t < k then
      if selected r ⟨t, ht⟩ then
        Expr.mux (.input (.inl ⟨t, ht⟩)) (previousExpr r j) (.input (.inr (r, j)))
      else .input (.inr (r, j))
    else .input (.inr (r, j))

variable [Fintype Rows]

private noncomputable def scan (selected : Rows → Fin k → Bool) (t : ℕ) :
    Frame (Input Rows k) (Input Rows k) :=
  ((Frame.initial id).step initialExpr).steps (layerExpr selected) t

private theorem scan_eval (selected : Rows → Fin k → Bool) (x : Input Rows k → Bool) (t : ℕ) :
    (∀ i, (scan selected t).eval x (.inl i) = x (.inl i)) ∧
    (∀ r j, (scan selected t).eval x (.inr (r,j)) =
      decide (prefixCount selected (x ∘ Sum.inl) r t = j.val)) := by
  induction t with
  | zero =>
    constructor <;> intros <;> simp [scan, initialExpr, Expr.eval, prefixCount]
  | succ t ih =>
    have hs : scan selected (t+1) = (scan selected t).step (layerExpr selected t) := rfl
    constructor
    · intro i
      simpa [hs, layerExpr, Expr.eval] using ih.1 i
    · intro r j
      rw [hs, Frame.step_eval]
      have hc : prefixCount selected (x ∘ Sum.inl) r (t+1) =
          prefixCount selected (x ∘ Sum.inl) r t +
          (if ht : t < k then (if selected r ⟨t,ht⟩ && x (.inl ⟨t,ht⟩) then 1 else 0)
            else 0) := Finset.sum_range_succ _ _
      rw [hc]
      by_cases ht : t < k
      · cases hr : selected r ⟨t, ht⟩ <;> cases hx : x (.inl ⟨t,ht⟩) <;>
          simp [layerExpr, ht, hr, hx, ih.1, ih.2, Expr.eval]
        by_cases hj : j.val = 0
        · simp [previousExpr, hj, Expr.eval]
        · simp only [previousExpr, ite_eq_right hj, Expr.eval, ih.2]
          apply Bool.eq_iff_iff.mpr
          simp
          omega
      · simp [layerExpr, ht, Expr.eval, ih.2]

/-- The completed table of attained counts, before checking the supplied target. -/
noncomputable def counters (selected : Rows → Fin k → Bool) :
    Frame (Input Rows k) (Rows × Fin (k+1)) :=
  (scan selected k).select Sum.inr

theorem counters_eval (selected : Rows → Fin k → Bool) (input : Input Rows k → Bool)
    (r : Rows) (j : Fin (k+1)) :
    (counters selected).eval input (r,j) = decide (rowCount selected (input ∘ Sum.inl) r = j.val) := by
  simp only [counters, Frame.select_eval, (scan_eval selected input k).2, prefixCount_full]

private def mismatch (a : Rows × Fin (k+1)) : Expr (Input Rows k ⊕ Input Rows k) :=
  let target := Expr.input (.inl (.inr a))
  let attained := Expr.input (.inr (.inr a))
  Expr.mux target (.not attained) attained

omit [Fintype Rows] in
private theorem mismatch_eval (v : Input Rows k ⊕ Input Rows k → Bool) (a : Rows × Fin (k+1)) :
    (mismatch a).eval v = true ↔ v (.inl (.inr a)) ≠ v (.inr (.inr a)) := by
  cases ht : v (.inl (.inr a)) <;> cases hc : v (.inr (.inr a)) <;>
    simp [mismatch, Expr.eval, ht, hc]

private noncomputable def outputExpr (_ : Unit) : Expr (Input Rows k ⊕ Input Rows k) :=
  .not (Expr.disjoin (Finset.univ.toList.map mismatch))

/-- Finished network over both the flag bits and the queried target table. -/
noncomputable def frame (selected : Rows → Fin k → Bool) : Frame (Input Rows k) Unit :=
  (scan selected k).withInput.step outputExpr

/-- The output rejects every differing entry, including extra marks in a target row. -/
theorem frame_eval_iff (selected : Rows → Fin k → Bool) (x : Fin k → Bool)
    (target : Rows → Fin (k+1) → Bool) :
    (frame selected).eval (Sum.elim x (Function.uncurry target)) () = true ↔
      RowCountsOK selected x target := by
  simp only [frame, Frame.step_eval, outputExpr, Expr.eval, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  simp only [ne_eq, Expr.eval_disjoin_true,  List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    exists_exists_eq_and, mismatch_eval, not_exists, not_not, Frame.withInput_eval_inl,
    Frame.withInput_eval_inr, Sum.elim_inr]
  simp only [Prod.forall, (scan_eval selected _ k).2, prefixCount_full]
  rfl

/-- Deterministic transcript verifier for the row counts. -/
noncomputable def verifier (selected : Rows → Fin k → Bool) :=
  (frame selected).circuit ()

theorem verifier_eval_iff (selected : Rows → Fin k → Bool) (x : Fin k → Bool)
    (target : Rows → Fin (k+1) → Bool) :
    (verifier selected).eval (Sum.elim x (Function.uncurry target)) = true ↔
      RowCountsOK selected x target := by
  rw [verifier, Frame.circuit_eval, frame_eval_iff]

omit [Fintype Rows] in
private theorem layerExpr_size (selected : Rows → Fin k → Bool) (t : ℕ) (i : Input Rows k) :
    (layerExpr selected t i).size ≤ 8 := by
  rcases i with i | ⟨r,j⟩
  · change 1 ≤ 8
    decide
  · by_cases ht : t < k
    · cases hr : selected r ⟨t,ht⟩ <;> by_cases hj : j.val = 0 <;>
        simp [layerExpr, ht, hr, hj, Expr.mux, Expr.size, previousExpr]
    · simp [layerExpr, ht, Expr.size]

private theorem outputExpr_size (u : Unit) :
    (outputExpr (Rows := Rows) (k := k) u).size ≤ Fintype.card Rows * (k+1) * 10 + 2 := by
  have hs := Expr.size_disjoin_le (Finset.univ.toList.map (mismatch (Rows := Rows) (k := k))) 9
    (fun e he ↦ by obtain ⟨a, _, rfl⟩ := List.mem_map.mp he; rfl)
  simp only [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin] at hs
  exact Nat.add_le_add_right hs 1

/-- One constant-size local expression per live wire at every clock tick, followed by
one constant-size mismatch check per table entry and a disjunction. -/
theorem frame_size_le (selected : Rows → Fin k → Bool) :
    (frame selected).size ≤
      (k + Fintype.card Rows * (k+1)) + k * ((k + Fintype.card Rows * (k+1)) * 8) +
        (Fintype.card Rows * (k+1) * 10 + 2) := by
  let first : Frame (Input Rows k) (Input Rows k) := (Frame.initial id).step initialExpr
  have hi : first.size ≤ Fintype.card (Input Rows k) := by
    have h := Frame.step_size_le (Frame.initial id) (initialExpr (Rows := Rows) (k := k)) 1
      (by rintro (i | ⟨r,j⟩) <;> rfl)
    simpa [first] using h
  have hs := Frame.steps_size_le first (layerExpr selected) k 8 (fun t _ i ↦ layerExpr_size _ t i)
  have hf := Frame.step_size_le (scan selected k).withInput outputExpr
    (Fintype.card Rows * (k+1) * 10 + 2) outputExpr_size
  simp only [Frame.withInput_size, Fintype.card_unit, one_mul] at hf
  change (frame selected).size ≤ (first.steps (layerExpr selected) k).size + _ at hf
  simp only [Input, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hi hs
  omega

/-- Size bound in the AND/NOT gate model used by the transcript verifier. -/
theorem verifier_size_le (selected : Rows → Fin k → Bool) :
    (frame selected).circuitSize () ≤ 4 *
      ((k + Fintype.card Rows * (k+1)) + k * ((k + Fintype.card Rows * (k+1)) * 8) +
        (Fintype.card Rows * (k+1) * 10 + 2)) :=
  ((frame selected).circuitSize_le ()).trans (Nat.mul_le_mul_left _ (frame_size_le selected))

end OracleTally

end VPVNP
end Computability
end OAI
