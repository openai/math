import OAI.Optimization.LinearProgramming.PrimalDual.Bits
import OAI.Optimization.LinearProgramming.PrimalDual.Layout

/-! The dimensional and binary-size cost of the second oracle input in Corollary 1.2. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM

theorem ratBits_le_totalBits_of_mem {xs : List ℚ} {q : ℚ} (hq : q ∈ xs) : ratBits q ≤ totalBits xs := by
  induction xs with
  | nil => simp at hq
  | cons q' qs ih =>
    simp only [List.mem_cons] at hq
    change ratBits q ≤ ratBits q' + totalBits qs
    rcases hq with rfl | h
    · omega
    · exact (ih h).trans (Nat.le_add_left _ _)

private theorem length_le_totalBits (xs : List ℚ) : xs.length ≤ totalBits xs := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    change qs.length + 1 ≤ ratBits q + totalBits qs
    have : 1 ≤ ratBits q := by unfold ratBits; omega
    omega

private theorem totalBits_le_length_mul (xs : List ℚ) (B : ℕ) (hb : ∀ q ∈ xs, ratBits q ≤ B) :
    totalBits xs ≤ xs.length * B := by
  induction xs with
  | nil => simp [totalBits]
  | cons q qs ih =>
    change ratBits q + totalBits qs ≤ (qs.length+1)*B
    rw [Nat.succ_mul, Nat.add_comm _ B]
    exact Nat.add_le_add (hb q (by simp)) (ih (fun z hz => hb z (List.mem_cons_of_mem _ hz)))

/-- Even allowing zero dimensions, the original tape length dominates the sum of
dimensions because it includes one RHS scalar per row and one objective scalar per column. -/
theorem dimensions_le_optInputBits {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c : Fin d → ℚ) : m+d ≤ totalBits (lpInput A b ++ List.ofFn c) := by
  have h := length_le_totalBits (lpInput A b ++ List.ofFn c)
  rw [List.length_append, lpInput_length, List.length_ofFn] at h
  omega

/-- Full encoded length of the second call, including the dense zero blocks. -/
theorem jointInput_totalBits {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c : Fin d → ℚ) :
    let L := totalBits (lpInput A b ++ List.ofFn c)
    totalBits (lpInput (finJointMatrix A b c) (finJointRhs b c)) ≤ (2*L+1)*(L+1)*(L+3) := by
  let L := totalBits (lpInput A b ++ List.ofFn c)
  have hA (i j) : ratBits (A i j) ≤ L :=
    ratBits_le_totalBits_of_mem (List.mem_append_left _ (List.mem_of_getElem? (lpInput_matrix_word A b i j)))
  have hb (i) : ratBits (b i) ≤ L :=
    ratBits_le_totalBits_of_mem (List.mem_append_left _ (List.mem_of_getElem? (lpInput_rhs_word A b i)))
  have hc (j) : ratBits (c j) ≤ L :=
    ratBits_le_totalBits_of_mem (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
  have hM (i j) : ratBits (finJointMatrix A b c i j) ≤ L+3 :=
    ratBits_jointMatrix_le A b c (by omega)
      (fun i j => (hA i j).trans (by omega)) (fun i => (hb i).trans (by omega))
      (fun j => (hc j).trans (by omega)) _ _
  have hr (i) : ratBits (finJointRhs b c i) ≤ L+3 :=
    ratBits_jointRhs_le b c (by omega) (fun i => (hb i).trans (by omega))
      (fun j => (hc j).trans (by omega)) _
  have ht := totalBits_le_length_mul (lpInput (finJointMatrix A b c) (finJointRhs b c)) (L+3) (by
    intro q hq
    simp only [lpInput, List.mem_append, List.mem_flatten, List.mem_ofFn] at hq
    rcases hq with ⟨_,⟨i,rfl⟩,hm⟩ | ⟨i,rfl⟩
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hm
      exact hM i j
    · exact hr i)
  rw [lpInput_length] at ht
  have hd : m+d ≤ L := dimensions_le_optInputBits A b c
  calc
    _ ≤ ((m+(m+(d+(d+1))))*(d+m)+(m+(m+(d+(d+1)))))*(L+3) := ht
    _ = (2*(m+d)+1)*((m+d)+1)*(L+3) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))

/-- Summing both query bounds still uses a dimension-only polynomial. -/
theorem both_calls_step_bound (C E m d : ℕ) :
    polyBound C E (m+d) + polyBound C E ((m+(m+(d+(d+1))))+(d+m)) ≤
      2 * polyBound C E (3*(m+d)+1) := by
  have h₁ : polyBound C E (m+d) ≤ polyBound C E (3*(m+d)+1) :=
    Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) _)
  have h₂ : (m+(m+(d+(d+1))))+(d+m) = 3*(m+d)+1 := by omega
  rw [h₂]
  omega

end PrimalDual
end LinearProgramming
end Optimization
end OAI
