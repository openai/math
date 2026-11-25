import OAI.Optimization.LinearProgramming.Lattice.QueryTree
import Mathlib.Data.Nat.Size

/-! Coefficient size of every sign query in the rational matrix normalization procedure. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

namespace SignQueries

/-- The queries actually made, in reverse chronological order. -/
def history {p : ℕ} {α : Type*} (oracle : (Fin p → ℤ) → Bool) : SignQueries p α → List (Fin p → ℤ)
  | .done _ => []
  | .ask a next => history oracle (next (oracle a)) ++ [a]

@[simp] theorem history_bind {p : ℕ} {α β : Type*} (oracle : (Fin p → ℤ) → Bool)
    (t : SignQueries p α) (next : α → SignQueries p β) :
    history oracle (t.bind next) = history oracle (next (run oracle t)) ++ history oracle t := by
  induction t with
  | done x => simp [bind, run, history]
  | ask a child ih => simp only [bind, run, history, ih, List.append_assoc]

@[simp] theorem history_length {p : ℕ} {α : Type*} (oracle : (Fin p → ℤ) → Bool) (t : SignQueries p α) :
    (history oracle t).length = cost oracle t := by
  induction t with
  | done x => rfl
  | ask a next ih => simp [history, cost, ih]

@[simp] theorem mem_history_sequence {p n : ℕ} {α : Type*} (oracle : (Fin p → ℤ) → Bool)
    (f : Fin n → SignQueries p α) (row : Fin p → ℤ) :
    row ∈ history oracle (sequence n f) ↔ ∃ i, row ∈ history oracle (f i) := by
  induction n with
  | zero => simp [sequence, history]
  | succ n ih => simp [sequence, history, ih, Fin.exists_fin_succ, or_comm]

end SignQueries

@[simp] theorem maxRowQ_history {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (rows : List (Fin p → ℤ)) :
    SignQueries.history oracle (maxRowQ rows) = (maxAbsRow oracle rows).queries := by
  induction rows with
  | nil => rfl
  | cons a rows ih => simp [maxRowQ, maxAbsRow, SignQueries.history, ih]

@[simp] theorem dyadicSearchQ_history {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ) (k : ℕ) :
    SignQueries.history oracle (dyadicSearchQ a b k) = (dyadicSearch oracle a b k).queries := by
  induction k with
  | zero => rfl
  | succ k ih => simp [dyadicSearchQ, dyadicSearch, SignQueries.history, ih]

private theorem maxAbsRow_size {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (rows : List (Fin p → ℤ))
    {H : ℤ} (hH : 0 ≤ H) (hr : ∀ a ∈ rows, ∀ i, |a i| ≤ H) :
    (∀ i, |(maxAbsRow oracle rows).row i| ≤ H) ∧
    ∀ a ∈ (maxAbsRow oracle rows).queries, ∀ i, |a i| ≤ 2 * H := by
  induction rows with
  | nil => simp [maxAbsRow, hH]
  | cons a rs ih =>
    obtain ⟨hprev, hqs⟩ := ih (fun b hb ↦ hr b (List.mem_cons_of_mem _ hb))
    let oriented := if oracle a then a else -a
    have ha (i : Fin p) : |a i| ≤ H := hr a (List.mem_cons_self) i
    have hor (i : Fin p) : |oriented i| ≤ H := by
      dsimp only [oriented]
      split <;> simpa using ha i
    have hdiff (i : Fin p) : |(oriented - (maxAbsRow oracle rs).row) i| ≤ 2 * H :=
      (abs_sub ..).trans (by have := hor i; have := hprev i; linarith)
    constructor
    · intro i
      change |(if oracle (oriented - _) then oriented else _) i| ≤ H
      split
      · exact hor i
      · exact hprev i
    · intro b hb i
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hdiff i
      rcases List.mem_cons.mp hb with rfl | hb
      · linarith [ha i]
      · exact hqs b hb i

/-- Every queried integer coefficient fits in `k+1` bits beyond the size of a cleared input
coefficient (up to the extra sign bit). This bound holds for arbitrary Boolean replies. -/
theorem probeRowsQ_coefficient_bound {n p : ℕ} (oracle : (Fin p → ℤ) → Bool) (P : Fin n → Fin p → ℚ)
    (k : ℕ) {H : ℤ} (hH : 0 ≤ H) (hP : ∀ i j, |integralRows P i j| ≤ H) {row : Fin p → ℤ}
    (hmem : row ∈ SignQueries.history oracle (probeRowsQ P k)) (j : Fin p) : |row j| ≤ 2 ^ (k + 1) * H := by
  let rows := integralRows P
  let d := (maxAbsRow oracle (List.ofFn rows)).row
  have hm := maxAbsRow_size oracle (List.ofFn rows) hH (fun r hr i ↦ by
    obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hr
    exact hP s i)
  have hpow : (2 : ℤ) ≤ 2 ^ (k + 1) := by
    rw [pow_succ]; have := one_le_pow₀ (show (1 : ℤ) ≤ 2 by decide) (n := k); omega
  have hh := mul_le_mul_of_nonneg_right hpow hH
  simp only [probeRowsQ, SignQueries.history_bind, maxRowQ_run, SignQueries.history,
    List.mem_append, List.mem_singleton, maxRowQ_history] at hmem
  rcases hmem with (hp | hd) | hmax
  · change row ∈ SignQueries.history oracle (if oracle (-d) then _ else _) at hp
    split at hp
    · simp [SignQueries.history] at hp
    · simp only [SignQueries.history_bind, SignQueries.history, List.nil_append,
        SignQueries.mem_history_sequence, dyadicSearchQ_history] at hp
      obtain ⟨i, hi⟩ := hp
      have hs := dyadicSearch_query_coeff_bound oracle (rows i) d k hi j
      calc
        _ ≤ 2 ^ k * (|rows i j| + |d j|) := hs
        _ ≤ 2 ^ k * (H + H) := mul_le_mul_of_nonneg_left (add_le_add (hP i j) (hm.1 j)) (by positivity)
        _ = _ := by rw [pow_succ]; ring
  · subst row
    exact (abs_neg (d j) ▸ hm.1 j).trans (hh.trans' (by omega))
  · exact (hm.2 _ hmax j).trans hh

/-- Clearing an entry multiplies its numerator by a divisor of the common denominator. -/
theorem integralRows_size {n p : ℕ} (P : Fin n → Fin p → ℚ) (i : Fin n) (j : Fin p) :
    |integralRows P i j| ≤ (matrixDenominator P : ℤ) * |(P i j).num| := by
  simp only [integralRows, abs_mul, Int.natCast_nonneg, abs_of_nonneg]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self (matrixDenominator P) (P i j).den) (abs_nonneg _)

/-- A uniform entry-denominator bound turns into an explicit common-denominator height. -/
theorem matrixDenominator_le_pow {n p : ℕ} (P : Fin n → Fin p → ℚ) (M : ℕ)
    (h : ∀ i j, (P i j).den ≤ M) : matrixDenominator P ≤ M ^ (n * p) := by
  calc
    _ ≤ ∏ _ : Fin n, ∏ _ : Fin p, M := Finset.prod_le_prod fun i _ ↦ Finset.prod_le_prod fun j _ ↦ h i j
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

/-- In input bit bounds, every query has coefficient magnitude at most
`2^(k + 1 + bits*(np+1))`, independent of the hidden real vector. -/
theorem probeRowsQ_input_bit_bound {n p : ℕ} (oracle : (Fin p → ℤ) → Bool)
    (P : Fin n → Fin p → ℚ) (k bits : ℕ) (hn : ∀ i j, |(P i j).num| ≤ (2 : ℤ) ^ bits)
    (hd : ∀ i j, (P i j).den ≤ 2 ^ bits) {row : Fin p → ℤ}
    (hmem : row ∈ SignQueries.history oracle (probeRowsQ P k)) (j : Fin p) :
    |row j| ≤ 2 ^ (k + 1 + bits * (n * p + 1)) := by
  have hD : (matrixDenominator P : ℤ) ≤ ((2 : ℤ)^bits) ^ (n*p) := by
    exact_mod_cast matrixDenominator_le_pow P _ hd
  have hr (i a) : |integralRows P i a| ≤ ((2 : ℤ)^bits) ^ (n*p+1) := by
    rw [pow_succ]
    exact (integralRows_size P i a).trans (mul_le_mul hD (hn i a) (abs_nonneg _) (by positivity))
  have hh := probeRowsQ_coefficient_bound oracle P k (by positivity) hr hmem j
  simpa only [pow_add, pow_mul] using hh

theorem int_abs_lt_two_pow_iff {z : ℤ} {L : ℕ} :
    |z| < (2 : ℤ) ^ L ↔ z.natAbs.size ≤ L := by
  rw [Nat.size_le, ← Nat.cast_lt (α := ℤ), Int.natCast_natAbs, Nat.cast_pow, Nat.cast_ofNat]

/-- Common denominator clearing costs at most `L * (n*p + 1)` bits per coefficient if each
signed numerator magnitude and each positive denominator needs at most `L` bits. -/
theorem integralRows_natAbs_size {n p L : ℕ} (P : Fin n → Fin p → ℚ)
    (h : ∀ i j, (P i j).num.natAbs.size ≤ L ∧ (P i j).den.size ≤ L) (i : Fin n) (j : Fin p) :
    (integralRows P i j).natAbs.size ≤ L * (n * p + 1) := by
  have hden := matrixDenominator_le_pow P (2^L) (fun s t ↦ (Nat.size_le.mp (h s t).2).le)
  have hd : (matrixDenominator P : ℤ) ≤ ((2 : ℤ)^L) ^ (n*p) := by exact_mod_cast hden
  apply int_abs_lt_two_pow_iff.mp
  calc
    |integralRows P i j| ≤ (matrixDenominator P : ℤ) * |(P i j).num| := integralRows_size P i j
    _ ≤ ((2 : ℤ)^L)^(n*p) * |(P i j).num| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
    _ < ((2 : ℤ)^L)^(n*p) * 2^L := mul_lt_mul_of_pos_left (int_abs_lt_two_pow_iff.mpr (h i j).1) (by positivity)
    _ = _ := by rw [pow_mul (2 : ℤ) L (n*p+1), pow_succ]

/-- Binary magnitude length of every coefficient of every actual sign query. -/
theorem probeRowsQ_natAbs_size {n p L : ℕ} (oracle : (Fin p → ℤ) → Bool)
    (P : Fin n → Fin p → ℚ) (k : ℕ) (h : ∀ i j, (P i j).num.natAbs.size ≤ L ∧ (P i j).den.size ≤ L)
    {row : Fin p → ℤ} (hm : row ∈ SignQueries.history oracle (probeRowsQ P k)) (j : Fin p) :
    (row j).natAbs.size ≤ k + 1 + L * (n * p + 1) := by
  let B := L * (n * p + 1)
  have hpow : (0 : ℤ) < 2^B := by positivity
  have hb (s t) : |integralRows P s t| ≤ 2 ^ B - 1 := by
    have hh : |integralRows P s t| < 2 ^ B := int_abs_lt_two_pow_iff.mpr (integralRows_natAbs_size P h s t)
    omega
  apply int_abs_lt_two_pow_iff.mp
  rw [pow_add]
  exact (probeRowsQ_coefficient_bound oracle P k (by omega) hb hm j).trans_lt
    (mul_lt_mul_of_pos_left (sub_one_lt _) (by positivity))

end Lattice
end LinearProgramming
end Optimization
end OAI
