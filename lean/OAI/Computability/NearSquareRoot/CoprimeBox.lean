import OAI.Computability.NearSquareRoot.BoxScale
import OAI.Computability.NearSquareRoot.BoxShape
import OAI.Computability.NearSquareRoot.BoxDensity
import OAI.NumberTheory.Jacobsthal.Conclusions.QuadraticBound

/-!
# Deterministic construction of the coprime axes

Instead of testing for primes in short intervals, test gcd against twice the
product of the moduli already selected. These tests deterministically produce
odd, pairwise coprime axis lengths. The quadratic Jacobsthal bound guarantees a
successful test because the accumulated product has at most `k+1` prime divisors.
The search window is a polynomial in `k` and is specified independently of the
constant in the Jacobsthal theorem.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CoprimeBox

open BoxScale

/-- Search the closed interval `[lo,lo+h]` downwards. -/
def search (lo acc : ℕ) : ℕ → ℕ
  | 0 => lo
  | h + 1 => if (lo + (h + 1)).Coprime acc then lo + (h + 1) else search lo acc h

theorem search_mem (lo acc h : ℕ) : lo ≤ search lo acc h ∧ search lo acc h ≤ lo + h := by
  induction h with
  | zero => simp [search]
  | succ h ih => simp only [search]; split <;> omega

theorem search_coprime {lo acc h : ℕ} (w : ∃ j ≤ h, (lo + j).Coprime acc) :
    (search lo acc h).Coprime acc := by
  induction h with
  | zero => simpa [search] using w
  | succ h ih =>
    simp only [search]
    split
    · assumption
    · rename_i miss
      apply ih
      obtain ⟨j, hj, hgood⟩ := w
      exact ⟨j, by by_contra! hlarge; exact miss (by rwa [show h + 1 = j by omega]), hgood⟩

def window (k : ℕ) : ℕ := span k / k^2

/-- Add full-width axes one at a time. A gcd is taken with the product accumulated so far. -/
def fullAxes (k : ℕ) : ℕ → List ℕ
  | 0 => []
  | m + 1 =>
    let as := fullAxes k m
    search (span k - window k) (2 * as.prod) (window k) :: as

@[simp] theorem length_fullAxes (k m : ℕ) : (fullAxes k m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [fullAxes, ih]

theorem window_fits {k : ℕ} (hk : 2 ≤ k) : 2 * k * window k ≤ span k := by
  calc
    2 * k * window k ≤ k ^ 2 * window k := Nat.mul_le_mul_right _ (by nlinarith)
    _ ≤ span k := Nat.mul_div_le ..

private theorem span_lower {k : ℕ} (hk : 2 ≤ k) : 2 ≤ span k - window k := by
  have h₁ : 4 * window k ≤ span k := le_trans (Nat.mul_le_mul_right _ (by omega : 4 ≤ 2 * k)) (window_fits hk)
  have h₂ : 4 ≤ span k := by
    exact (show 4 ≤ 2 ^ 20 by decide).trans ((Nat.pow_le_pow_left hk 20).trans (pow_le_span k))
  omega

theorem fullAxes_mem {k m a : ℕ} (ha : a ∈ fullAxes k m) :
    span k - window k ≤ a ∧ a ≤ span k := by
  have hw : window k ≤ span k := Nat.div_le_self ..
  induction m with
  | zero => simp [fullAxes] at ha
  | succ m ih =>
    rw [fullAxes, List.mem_cons] at ha
    rcases ha with rfl | ha
    · simpa [Nat.sub_add_cancel hw] using search_mem (span k - window k) (2 * (fullAxes k m).prod) (window k)
    · exact ih ha

private theorem prime_count_of_size {p k : ℕ} (hp : 0 < p) (hb : p ≤ 2 ^ k) :
    p.primeFactors.card ≤ k := by
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  calc
    2 ^ p.primeFactors.card = ∏ _ ∈ p.primeFactors, 2 := by simp
    _ ≤ ∏ q ∈ p.primeFactors, q := Finset.prod_le_prod fun q hq => (Nat.prime_of_mem_primeFactors hq).two_le
    _ ≤ p := Nat.le_of_dvd hp (Nat.prod_primeFactors_dvd p)
    _ ≤ _ := hb

private theorem next_witness {k m b : ℕ} (hk : 2 ≤ k) (hm : m ≤ count k)
    (hjac : Erdos970.NumberTheoryLean.Targets.IsJacobsthalBound (k+1) b)
    (hb : b ≤ window k) :
    ∃ j ≤ window k, (span k - window k + j).Coprime (2 * (fullAxes k m).prod) := by
  let as := fullAxes k m
  have ha : 0 < 2 * as.prod := Nat.mul_pos (by decide) <| List.prod_pos fun a h =>
    lt_of_lt_of_le (by omega : 0 < 2) ((span_lower hk).trans (fullAxes_mem h).1)
  have hpow : (2 : ℕ) * as.prod ≤ 2^(k+1) := by
    calc
      2 * as.prod ≤ 2 * (span k)^m := Nat.mul_le_mul_left _ (by
        simpa [as] using List.prod_le_pow_length as (span k) (fun a h => (fullAxes_mem h).2))
      _ = 2 * 2 ^ (width k * m) := by rw [span, pow_mul]
      _ ≤ 2 * 2 ^ k := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by decide)
        rw [Nat.mul_comm]
        exact (Nat.mul_le_mul_right _ hm).trans (count_mul_le k)
      _ = 2 ^ (k+1) := by rw [pow_succ, mul_comm]
  obtain ⟨j, hj, hgood⟩ := hjac _ ha (prime_count_of_size ha hpow) ((span k - window k : ℕ) : ℤ)
  refine ⟨j, by omega, ?_⟩
  simpa only [← Int.natCast_add, Int.natAbs_natCast] using hgood

private theorem fullAxes_of_bound {k b : ℕ} (hk : 2 ≤ k)
    (hjac : Erdos970.NumberTheoryLean.Targets.IsJacobsthalBound (k+1) b) (hb : b ≤ window k)
    (m : ℕ) (hm : m ≤ count k) :
    (fullAxes k m).Pairwise Nat.Coprime ∧ ∀ a ∈ fullAxes k m, Odd a := by
  induction m with
  | zero => simp [fullAxes]
  | succ m ih =>
    have hprev : m ≤ count k := by omega
    obtain ⟨hpair, hodd⟩ := ih hprev
    have hnew := Nat.coprime_mul_iff_right.mp <| search_coprime <| next_witness hk hprev hjac hb
    simp only [fullAxes, List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨⟨fun a ha => hnew.2.of_dvd_right (List.dvd_prod ha), hpair⟩,
      Nat.coprime_two_right.mp hnew.1, hodd⟩

/-- For every sufficiently large address width the executable gcd search succeeds on every axis. -/
theorem eventually_fullAxes : ∃ K : ℕ, ∀ k ≥ K,
    (fullAxes k (count k)).Pairwise Nat.Coprime ∧ ∀ a ∈ fullAxes k (count k), Odd a := by
  obtain ⟨C, _, hC⟩ := Erdos970.Erdos970Final.erdos_970_quadratic
  refine ⟨max 2 (4 * ⌈C⌉₊), ?_⟩
  intro k hk
  obtain ⟨m, hjac, hm⟩ := hC (k+1) (by omega)
  apply fullAxes_of_bound ((le_max_left ..).trans hk) hjac _ _ (le_refl _)
  apply le_trans _ (room ⌈C⌉₊ hk)
  exact_mod_cast hm.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (sq_nonneg _))

/-- Padded widths and actual cyclic orders, ready for the CRT reindexing. -/
def box (k : ℕ) : List (ℕ × ℕ) :=
  BoxShape.axes k (width k) (fullAxes k (count k))

/-- The same executable box construction works at every sufficiently large size. -/
theorem eventually_valid : ∃ K : ℕ, ∀ k ≥ K, BoxShape.Valid k (width k) (box k) := by
  obtain ⟨K, hK⟩ := eventually_fullAxes
  refine ⟨max K 2, ?_⟩
  intro k hk
  have hk2 : 2 ≤ k := (le_max_right ..).trans hk
  have hvalid := hK k ((le_max_left ..).trans hk)
  refine BoxShape.valid_axes (width_pos hk2) _ (length_fullAxes ..) ?_ hvalid.2 hvalid.1 ?_
  · exact fun a h => ⟨(span_lower hk2).trans (fullAxes_mem h).1, (fullAxes_mem h).2⟩
  · refine box_half_occupied _ (span k) (window k) k (Nat.pow_pos (by decide : 0 < 2)) ?_ (window_fits hk2) ?_
    · simpa using count_le k
    · exact fun a h => (fullAxes_mem h).1

/-- A tape implementation can replace the single product gcd by scanning the
previous moduli one at a time, so each arithmetic operand besides the address
width itself fits in a single short axis. -/
theorem test_iff (a : ℕ) (as : List ℕ) :
    a.Coprime (2 * as.prod) ↔ Odd a ∧ ∀ b ∈ as, a.Coprime b := by
  rw [Nat.coprime_mul_iff_right, Nat.coprime_two_right]
  apply and_congr_right
  intro _
  induction as with
  | nil => simp
  | cons b as ih => simp [Nat.coprime_mul_iff_right, ih]

end CoprimeBox

end NearSquareRoot
end Computability
end OAI
