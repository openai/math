import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import OAI.Optimization.LinearProgramming.Compression.RationalMinorSize

/-! Bounds on the data stored while tabulating Bird's division-free determinant recurrence.
A partial sum may use any subset of terms, so the bounds also apply before a sum is finished. -/

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- The matrices written after each pass through Bird's recurrence, with pass zero the input. -/
def birdLayer {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    ℕ → Matrix (Fin n) (Fin n) R
  | 0 => A
  | t + 1 => BirdDet.Spec.stepEntry A (birdLayer A t)

theorem birdLayer_eq_iterate {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (t : ℕ) :
    birdLayer A t = (BirdDet.Spec.stepEntry A)^[t] A := by
  induction t with
  | zero => rfl
  | succ t ih => rw [birdLayer, ih, Function.iterate_succ_apply']

/-- A scalar register of an entry computation, including both partially accumulated sums. -/
inductive BirdRegister (n : ℕ) where
  | input (i j : Fin n)
  | previous (i j : Fin n)
  | diagonal (s : Finset (Fin n))
  | negDiagonal (s : Finset (Fin n))
  | diagonalProduct (s : Finset (Fin n)) (i j : Fin n)
  | product (i k j : Fin n)
  | dotPartial (s : Finset (Fin n)) (i j : Fin n)
  | output (s u : Finset (Fin n)) (i j : Fin n)

/-- A symbolic register is read from the input and the preceding materialized layer. -/
def BirdRegister.read {R : Type*} [CommRing R] {n : ℕ}
    (A F : Matrix (Fin n) (Fin n) R) : BirdRegister n → R
  | .input i j => A i j
  | .previous i j => F i j
  | .diagonal s => ∑ k ∈ s, F k k
  | .negDiagonal s => -(∑ k ∈ s, F k k)
  | .diagonalProduct s i j => -(∑ k ∈ s, F k k) * A i j
  | .product i k j => F i k * A k j
  | .dotPartial s i j => ∑ k ∈ s, F i k * A k j
  | .output s u i j => -(∑ k ∈ s, F k k) * A i j + ∑ k ∈ u, F i k * A k j

/-- If all input entries have a common denominator `D`, this is the power of `D`
that clears the register during the pass from layer `t` to layer `t+1`. -/
def BirdRegister.denPower {n : ℕ} (t : ℕ) : BirdRegister n → ℕ
  | .input .. => 1
  | .previous .. | .diagonal .. | .negDiagonal .. => t + 1
  | .diagonalProduct .. | .product .. | .dotPartial .. | .output .. => t + 2

theorem birdLayer_succ_entry {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (t : ℕ) (i j : Fin n) :
    birdLayer A (t + 1) i j = BirdRegister.read A (birdLayer A t)
      (.output (Finset.Ioi i) (Finset.Ioi i) i j) := rfl

private theorem sum_natAbs_le_card_mul {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℤ)
    {B : ℕ} (h : ∀ i, (f i).natAbs ≤ B) : (∑ i ∈ s, f i).natAbs ≤ n * B := by
  calc
    _ ≤ ∑ i ∈ s, (f i).natAbs := Int.natAbs_sum_le s f
    _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum (fun i _ => h i)
    _ ≤ n * B := by simpa using Nat.mul_le_mul_right B (Finset.card_le_univ s)

/-- One pass on integer matrices increases the absolute-entry bound by a fixed factor.
The factor applies to registers of partial sums even if they later cancel in the output. -/
theorem birdRegister_natAbs_le {n H B : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ H) (hF : ∀ i j, (F i j).natAbs ≤ B)
    (hB : 1 ≤ B) (r : BirdRegister n) :
    (r.read A F).natAbs ≤ B * (2 * (n + 1) * (H + 1)) := by
  have hd (s) := sum_natAbs_le_card_mul s (fun k => F k k) (fun k => hF k k)
  have hp (i k j) : (F i k * A k j).natAbs ≤ B * H := by
    simpa only [Int.natAbs_mul] using Nat.mul_le_mul (hF i k) (hA k j)
  have ht (s i j) := sum_natAbs_le_card_mul s (fun k => F i k * A k j) (fun k => hp i k j)
  have hw (s i j) : (-(∑ k ∈ s, F k k) * A i j).natAbs ≤ n * B * H := by
    simpa only [Int.natAbs_mul, Int.natAbs_neg] using Nat.mul_le_mul (hd s) (hA i j)
  have hHa : H ≤ B * H := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right H hB
  cases r with
  | input i j => exact (hA i j).trans (by nlinarith only [hHa])
  | previous i j => exact (hF i j).trans (by nlinarith)
  | diagonal s => exact (hd s).trans (by nlinarith)
  | negDiagonal s => simpa only [BirdRegister.read, Int.natAbs_neg] using (hd s).trans (by nlinarith : n * B ≤ _)
  | diagonalProduct s i j => exact (hw s i j).trans (by nlinarith)
  | product i k j => exact (hp i k j).trans (by nlinarith)
  | dotPartial s i j => exact (ht s i j).trans (by nlinarith)
  | output s u i j =>
    exact (Int.natAbs_add_le ..).trans ((Nat.add_le_add (hw s i j) (ht u i j)).trans (by nlinarith))

theorem birdLayer_natAbs_le {n H : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ H) (t : ℕ) (i j : Fin n) :
    (birdLayer A t i j).natAbs ≤ (2 * (n + 1) * (H + 1)) ^ (t + 1) := by
  induction t generalizing i j with
  | zero => simpa [birdLayer] using (hA i j).trans (by nlinarith : H ≤ 2 * (n+1) * (H+1))
  | succ t ih =>
    rw [birdLayer_succ_entry, pow_succ]
    exact birdRegister_natAbs_le _ _ hA ih (Nat.succ_le_of_lt (pow_pos (by positivity) _)) _

theorem birdRegister_natAbs_le_pow {n H : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ H) (t : ℕ) (r : BirdRegister n) :
    (r.read A (birdLayer A t)).natAbs ≤ (2 * (n + 1) * (H + 1)) ^ (t + 2) := by
  rw [pow_succ]
  exact birdRegister_natAbs_le _ _ hA (birdLayer_natAbs_le A hA t) (Nat.succ_le_of_lt (pow_pos (by positivity) _)) r

private theorem birdRegister_scale {n : ℕ} (D : ℚ) (t : ℕ)
    (C G : Matrix (Fin n) (Fin n) ℤ) (A F : Matrix (Fin n) (Fin n) ℚ)
    (hc : ∀ i j, (C i j : ℚ) = D * A i j)
    (hg : ∀ i j, (G i j : ℚ) = D ^ (t + 1) * F i j) (r : BirdRegister n) :
    ((r.read C G : ℤ) : ℚ) = D ^ (r.denPower t) * r.read A F := by
  have hdiag (s : Finset (Fin n)) : ((∑ k ∈ s, G k k : ℤ) : ℚ) =
      D ^ (t+1) * ∑ k ∈ s, F k k := by simp only [Int.cast_sum, Finset.mul_sum, hg]
  have hprod (i k j : Fin n) : ((G i k * C k j : ℤ) : ℚ) = D^(t+2) * (F i k * A k j) := by
    rw [Int.cast_mul, hg, hc, pow_succ D (t+1)]; ring
  have hdot (s : Finset (Fin n)) (i j : Fin n) : ((∑ k ∈ s, G i k * C k j : ℤ) : ℚ) =
      D^(t+2) * ∑ k ∈ s, F i k * A k j := by simp only [Int.cast_sum, Finset.mul_sum, hprod]
  have hmul (s : Finset (Fin n)) (i j : Fin n) :
      ((-(∑ k ∈ s, G k k) * C i j : ℤ) : ℚ) = D^(t+2) * (-(∑ k ∈ s, F k k) * A i j) := by
    rw [Int.cast_mul, Int.cast_neg, hdiag, hc, pow_succ D (t+1)]; ring
  cases r with
  | input i j => simpa [BirdRegister.denPower, BirdRegister.read] using hc i j
  | previous i j => exact hg i j
  | diagonal s => exact hdiag s
  | negDiagonal s => simp [BirdRegister.read, BirdRegister.denPower, Int.cast_neg, hdiag]
  | diagonalProduct s i j => exact hmul s i j
  | product i k j => exact hprod i k j
  | dotPartial s i j => exact hdot s i j
  | output s u i j => simp only [BirdRegister.read, BirdRegister.denPower, Int.cast_add, hmul, hdot, mul_add]

theorem birdLayer_scale {n : ℕ} (D : ℚ) (C : Matrix (Fin n) (Fin n) ℤ)
    (A : Matrix (Fin n) (Fin n) ℚ) (hc : ∀ i j, (C i j : ℚ) = D * A i j)
    (t : ℕ) (i j : Fin n) :
    ((birdLayer C t i j : ℤ) : ℚ) = D ^ (t + 1) * birdLayer A t i j := by
  induction t generalizing i j with
  | zero => simpa [birdLayer] using hc i j
  | succ t ih =>
    rw [birdLayer_succ_entry, birdLayer_succ_entry]
    exact birdRegister_scale D t C _ A _ hc ih _

/-- A single numerator of controlled size represents each rational intermediate over a shared
power of the input denominator, irrespective of cancellation and reduction to lowest terms. -/
theorem birdRegister_height_of_scale {n H D : ℕ} (hD : 0 < D)
    (C : Matrix (Fin n) (Fin n) ℤ) (A : Matrix (Fin n) (Fin n) ℚ)
    (hc : ∀ i j, (C i j : ℚ) = (D : ℚ) * A i j) (hC : ∀ i j, (C i j).natAbs ≤ H)
    (t : ℕ) (r : BirdRegister n) :
    let x := r.read A (birdLayer A t)
    x.num.natAbs ≤ (2 * (n+1) * (H+1)) ^ (t+2) ∧ x.den ≤ D ^ (t+2) := by
  let z := r.read C (birdLayer C t)
  have he := birdRegister_scale (D : ℚ) t C _ A _ hc (birdLayer_scale D C A hc t) r
  have hd : 0 < D ^ (r.denPower t) := pow_pos hD _
  have hx : r.read A (birdLayer A t) = (z : ℚ) / ((D ^ r.denPower t : ℕ) : ℤ) := by
    apply (eq_div_iff (by positivity)).2
    have hpow : (((D ^ r.denPower t : ℕ) : ℤ) : ℚ) = (D : ℚ) ^ r.denPower t := by norm_cast
    rw [hpow, mul_comm]; exact he.symm
  have h := reduced_fraction_height z ((D ^ r.denPower t : ℕ) : ℤ) (by positivity)
  rw [← hx, Int.natAbs_natCast] at h
  exact ⟨h.1.trans (birdRegister_natAbs_le_pow C hC t r),
    h.2.trans (Nat.pow_le_pow_right hD (by cases r <;> simp [BirdRegister.denPower]))⟩

/-- A fixed polynomial in dimension and input-bit bound controls intermediate *reduced*
rational encoding lengths. The pass counter can be bounded by `n` in the determinant algorithm. -/
theorem birdRegister_bits {n B : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hbit : ∀ i j, RAM.ratBits (A i j) ≤ B) (t : ℕ) (r : BirdRegister n) :
    RAM.ratBits (r.read A (birdLayer A t)) ≤ 3 + (n + B + 2*B*n^2 + 3) * (t+2) := by
  have heights (i j : Fin n) : (A i j).num.natAbs ≤ 2^B ∧ (A i j).den ≤ 2^B := by
    have h := hbit i j
    unfold RAM.ratBits at h
    constructor <;> exact Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨D, C, hD, hd, hc, hm⟩ := exists_scaled_integer_matrix A
    (fun i j => (heights i j).1) (fun i j => (heights i j).2)
  obtain ⟨hnum, hden⟩ := birdRegister_height_of_scale hD C A hc hm t r
  rw [← pow_mul] at hd
  have hw : 2 ^ B * D ≤ 2 ^ (B + B*n^2) := by
    rw [pow_add]; exact Nat.mul_le_mul_left _ hd
  have hs : 2 ^ B * D + 1 ≤ 2 ^ (B + B*n^2 + 1) := by
    rw [pow_succ]; have := Nat.two_pow_pos (B+B*n^2); omega
  have hr : 2 * (n + 1) * (2 ^ B * D + 1) ≤ 2 ^ (n + B + B*n^2 + 3) := calc
    _ ≤ 2 * (2 ^ (n+1)) * 2 ^ (B+B*n^2+1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (n+1).lt_two_pow_self.le) hs
    _ = _ := by rw [Nat.mul_comm 2 (2 ^ (n+1)), ← pow_succ, ← pow_add]; congr 1; omega
  have hn := hnum.trans (Nat.pow_le_pow_left hr (t+2))
  have hz := hden.trans (Nat.pow_le_pow_left hd (t+2))
  rw [← pow_mul] at hn hz
  unfold RAM.ratBits
  calc
    _ ≤ 3 + (n+B+B*n^2+3)*(t+2) + (B*n^2)*(t+2) :=
      Nat.add_le_add (Nat.add_le_add_left (log2_le_of_le_two_pow hn) _) (log2_le_of_le_two_pow hz)
    _ = _ := by ring

end Compression
end LinearProgramming
end Optimization
end OAI
