import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-! # Recovering ordinary radix coefficients from cyclic convolution

The transform on the occupied addresses computes a cyclic sum. When each
operand occupies its first `h` positions and the cycle has at least `2*h`
positions, each contributing pair has its ordinary sum as residue. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

open Finset

/-- Ordinary convolution of unsigned digits, indexed by their natural positions. -/
def ordinaryCoefficient {S : ℕ} (x y : Fin S → ℕ) (t : Fin S) : ℕ :=
  ∑ i, ∑ j, if i.val + j.val = t.val then x i * y j else 0

/-- Express an array indexed by ranks as complex entries in cyclic coordinates. -/
def cyclicDigit {S : ℕ} [NeZero S] (x : Fin S → ℕ) (i : ZMod S) : ℂ :=
  x ((ZMod.finEquiv S).symm i)

/-- For a sufficiently padded product the cyclic difference lookup computes
the ordinary coefficient, including at positions in the zero tail. -/
theorem ordinaryCoefficient_eq_cyclic {S h : ℕ} [NeZero S]
    (x y : Fin S → ℕ) (hx : ∀ i, h ≤ i.val → x i = 0)
    (hy : ∀ j, h ≤ j.val → y j = 0) (hS : 2*h ≤ S) (t : Fin S) :
    ordinaryCoefficient x y t = ∑ i, x i * y (t - i) := by
  unfold ordinaryCoefficient
  refine sum_congr rfl fun i _ => ?_
  have he (j : Fin S) :
      (if i.val + j.val = t.val then x i * y j else 0) =
      (if j = t - i then x i * y j else 0) := by
    rcases lt_or_ge i.val h with hi | hi
    · rcases lt_or_ge j.val h with hj | hj
      · have hn : i.val + j.val < S := by omega
        have hiff : i.val + j.val = t.val ↔ j = t - i := by
          rw [eq_sub_iff_add_eq, add_comm j, Fin.ext_iff, Fin.val_add, Nat.mod_eq_of_lt hn]
        simp only [hiff]
      · simp [hy j hj]
    · simp [hx i hi]
  simp_rw [he]
  simp

/-- The complex sum delivered by the Fourier convolution has a natural
coefficient as its exact value. -/
theorem cyclicDigit_convolution {S h : ℕ} [NeZero S]
    (x y : Fin S → ℕ) (hx : ∀ i, h ≤ i.val → x i = 0)
    (hy : ∀ j, h ≤ j.val → y j = 0) (hS : 2*h ≤ S) (t : Fin S) :
    (∑ u : ZMod S, cyclicDigit x u * cyclicDigit y (ZMod.finEquiv S t - u)) =
      (ordinaryCoefficient x y t : ℂ) := by
  rw [ordinaryCoefficient_eq_cyclic x y hx hy hS]
  push_cast
  symm
  exact Fintype.sum_equiv (ZMod.finEquiv S).toEquiv _ _ fun i => by simp [cyclicDigit]

/-- Each coefficient is a sum of at most `h` products of two `b`-bit
digits, including on the zero-padded part of the cycle. -/
theorem ordinaryCoefficient_lt {S h b : ℕ} [NeZero S] (hh : 0 < h)
    (x y : Fin S → ℕ) (hx : ∀ i, h ≤ i.val → x i = 0)
    (hy : ∀ j, h ≤ j.val → y j = 0) (hS : 2*h ≤ S)
    (hxb : ∀ i, x i < 2^b) (hyb : ∀ j, y j < 2^b) (t : Fin S) :
    ordinaryCoefficient x y t < h * 2^(2*b) := by
  rw [ordinaryCoefficient_eq_cyclic x y hx hy hS]
  let stop : Fin S := ⟨h, by omega⟩
  let f (i : Fin S) := x i * y (t-i)
  have hsum : (∑ i ∈ Iio stop, f i) = ∑ i, f i := by
    apply sum_subset (subset_univ _)
    intro i _ hi
    have hle : h ≤ i.val := by simpa [stop, Fin.lt_def] using hi
    simp [f, hx i hle]
  change (∑ i, f i) < _
  rw [← hsum]
  calc
    _ < ∑ _i ∈ Iio stop, 2^(2*b) :=
      sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, mem_Iio.mpr hh⟩ fun i _ => by
        dsimp [f]
        rw [two_mul, pow_add]
        exact Nat.mul_lt_mul_of_lt_of_le (hxb i) (hyb _).le (by positivity)
    _ = _ := by simp [stop]

end NearSquareRoot
end Computability
end OAI
