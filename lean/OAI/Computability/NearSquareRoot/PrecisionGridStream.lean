import OAI.Computability.NearSquareRoot.PrecisionGrid
import OAI.Computability.NearSquareRoot.PrecisionPhaseStream

/-!
# Phase-table prefix multiplication on bounded records

The coefficient streams and operands can all use the grid for `2k+1`.
This leaves enough guard bits for the crude exponential error bound
`4^j` after at most `k` prefix multiplications. In particular neither
a stored prefix nor a local table entry can overflow the record.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication

/-- A few extra linear bits avoid changing record layouts between local
table construction, global phase streaming, and array arithmetic. -/
def guardedK (k : ℕ) := 2 * k + 1

private noncomputable abbrev tolerance (k : ℕ) : ℝ := 1 / (2 : ℝ) ^ (70 * k)

private theorem tolerance_le_one (k : ℕ) : tolerance k ≤ 1 :=
  (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

private theorem guard_absorbs {k j : ℕ} (hj : j ≤ k) :
    (4 : ℝ) ^ j * tolerance (guardedK k) ≤ tolerance k := by
  change (4 : ℝ) ^ j * (1 / _) ≤ 1 / _
  rw [← div_eq_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
    show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
  apply pow_le_pow_right₀ (by norm_num)
  unfold guardedK
  omega

private theorem phase_limit (k : ℕ) : 2 ≤ (2 : ℝ) ^ (13 * guardedK k) := by
  calc
    2 = (2 : ℝ) ^ (1 : ℕ) := by simp
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by unfold guardedK; omega)

private theorem norm_of_approx {r a : ℂ} (ha : ‖a‖ = 1)
    (hr : ‖r - a‖ ≤ 1) : ‖r‖ ≤ 2 := by
  have h := norm_add_le (r - a) a
  rw [sub_add_cancel, ha] at h
  linarith

/-- The represented product along one address remains close to its tensor
coefficient, charging one signed rounded multiplication at each block. -/
theorem multiply_prefix {α : Type*} (k : ℕ) (ideal : α → ℂ)
    (stored : α → Record (guardedK k)) (seed : Record (guardedK k))
    (hseed : value _ seed = 1) (xs : List α) (hlen : xs.length ≤ k)
    (hunit : ∀ x ∈ xs, ‖ideal x‖ = 1)
    (htable : ∀ x ∈ xs, ‖value _ (stored x) - ideal x‖ ≤ tolerance (guardedK k)) :
    ‖value _ (xs.foldl (fun p a => multiply _ p (stored a)) seed) - (xs.map ideal).prod‖ ≤
      tolerance k := by
  suffices h : ‖value _ (xs.foldl (fun p a => multiply _ p (stored a)) seed) -
      (xs.map ideal).prod‖ ≤ (4 : ℝ) ^ xs.length * tolerance (guardedK k) from
    h.trans (guard_absorbs hlen)
  induction xs using List.reverseRecOn with
  | nil => simp [hseed, tolerance]
  | append_singleton xs x ih =>
    have hlt : xs.length + 1 ≤ k := by simpa using hlen
    have hlen' : xs.length ≤ k := by omega
    have hacc := ih hlen' (fun t h => hunit t (by simp [h])) (fun t h => htable t (by simp [h]))
    have hx := hunit x (by simp)
    have hs := htable x (by simp)
    let a := (xs.map ideal).prod
    let p := xs.foldl (fun p t => multiply _ p (stored t)) seed
    change ‖value _ p - a‖ ≤ _ at hacc
    have ha : ‖a‖ = 1 := by
      unfold a
      rw [List.norm_prod]
      have hmap : (xs.map ideal).map (fun z => ‖z‖) = xs.map (fun _ => (1 : ℝ)) := by
        rw [List.map_map]
        apply List.map_congr_left
        exact fun t ht => hunit t (by simp [ht])
      rw [hmap]
      simp
    have hp : ‖value _ p‖ ≤ 2 := norm_of_approx ha
      (hacc.trans ((guard_absorbs hlen').trans (tolerance_le_one k)))
    have hb : ‖value _ (stored x)‖ ≤ 2 := norm_of_approx hx (hs.trans (tolerance_le_one _))
    have hm := multiply_error p (stored x) (hp.trans (phase_limit k)) (hb.trans (phase_limit k))
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append,
      List.map_singleton, List.prod_append, List.prod_singleton, List.length_append,
      List.length_singleton]
    change ‖value _ (multiply _ p (stored x)) - a * ideal x‖ ≤ _
    have delta :
        value _ (multiply _ p (stored x)) - a * ideal x =
          (value _ (multiply _ p (stored x)) - value _ p * value _ (stored x)) +
          ((value _ p - a) * value _ (stored x) + a * (value _ (stored x) - ideal x)) := by ring
    rw [delta]
    calc
      _ ≤ ‖value _ (multiply _ p (stored x)) - value _ p * value _ (stored x)‖ +
          (‖(value _ p - a) * value _ (stored x)‖ +
           ‖a * (value _ (stored x) - ideal x)‖) :=
        (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ tolerance (guardedK k) +
          ((4 : ℝ) ^ xs.length * tolerance (guardedK k) * 2 + tolerance (guardedK k)) := by
        rw [norm_mul, norm_mul, ha, one_mul]
        gcongr
      _ ≤ _ := by
        have hpw : 1 ≤ (4 : ℝ) ^ xs.length := one_le_pow₀ (by norm_num)
        have hd : 0 ≤ tolerance (guardedK k) := by unfold tolerance; positivity
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right hpw hd]

/-- Accuracy of every encoded coefficient produced by the table scans, in
the same order as the tensor addresses. -/
theorem phase_stream_error {α : Type*} (k : ℕ) (tables : List (List α))
    (ideal : α → ℂ) (stored : α → Record (guardedK k)) (seed : Record (guardedK k))
    (hseed : value _ seed = 1) (hlen : tables.length ≤ k)
    (hunit : ∀ tab ∈ tables, ∀ a ∈ tab, ‖ideal a‖ = 1)
    (htable : ∀ tab ∈ tables, ∀ a ∈ tab,
      ‖value _ (stored a) - ideal a‖ ≤ 1 / (2 : ℝ) ^ (70 * guardedK k)) :
    List.Forall₂ (fun r z => ‖value _ r - z‖ ≤ 1 / (2 : ℝ) ^ (70 * k))
      (tables.foldl (PhaseStream.extend (fun p a => multiply _ p (stored a))) [seed])
      ((PhaseStream.addresses tables).map (fun xs => (xs.map ideal).prod)) := by
  rw [PhaseStream.foldl_extend]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro xs hxs
  exact multiply_prefix k ideal stored seed hseed xs
    ((PhaseStream.length_of_mem_addresses hxs).le.trans hlen)
    (PhaseStream.forall_of_mem_addresses hxs hunit)
    (PhaseStream.forall_of_mem_addresses hxs htable)

end FixedPoint

end NearSquareRoot
end Computability
end OAI
