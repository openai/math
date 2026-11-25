import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic

/-! Quantitative loss of the product of the interior Gram determinants in an LLL swap. -/

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

private theorem finite_fold_mul {n : ℕ} (f : Fin n → ℕ) (a : ℕ) :
    Fin.foldl n (fun s i => s * f i) a = a * ∏ i, f i := by
  induction n generalizing a with
  | zero => simp
  | succ n ih => rw [Fin.foldl_succ, ih, Fin.prod_univ_succ, Nat.mul_assoc]

/-- The multiplicative potential over `d₁,…,dₙ₋₁`, excluding the trivial
zero-dimensional determinant and the invariant full Gram determinant. -/
def interiorGramPotential {n : ℕ} (d : Vector ℕ (n+1)) : ℕ :=
  Fin.foldl (n-1) (fun a i => a * d.get
    ⟨i.val+1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))⟩) 1

theorem interiorGramPotential_eq_prod {n : ℕ} (d : Vector ℕ (n+1)) :
    interiorGramPotential d = ∏ i : Fin (n-1), d.get
      ⟨i.val+1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))⟩ := by
  simp [interiorGramPotential, finite_fold_mul]

/-- A failed Lovász test at `δ=3/4` gives a strictly smaller pivot even
if the pivot update is written as integer floor division. -/
theorem swap_quotient_four_lt_three {a : ℤ} {d : ℕ} (ha : 0 ≤ a)
    (hfail : 4 * a < 3 * (d : ℤ)^2) :
    4 * (a / (d : ℤ)).toNat < 3 * d := by
  have hd : (0 : ℤ) < d := by
    by_contra! h
    have : (d : ℤ) = 0 := le_antisymm h (Int.natCast_nonneg _)
    rw [this] at hfail
    linarith
  have he : a / (d : ℤ) * (d : ℤ) ≤ a := Int.ediv_mul_le _ hd.ne'
  have h : 4 * (a / (d : ℤ)) < 3 * (d : ℤ) := by
    apply (mul_lt_mul_iff_of_pos_right hd).mp
    calc
      4 * (a / (d : ℤ)) * d = 4 * ((a / (d : ℤ)) * d) := by ring
      _ ≤ 4*a := by linarith
      _ < 3 * (d : ℤ) ^ 2 := hfail
      _ = (3 * (d : ℤ)) * d := by ring
  have hnonneg : 0 ≤ a / (d : ℤ) := Int.ediv_nonneg ha hd.le
  exact_mod_cast (show (4 : ℤ) * ((a / (d : ℤ)).toNat : ℤ) < 3 * (d : ℤ) by
    rwa [Int.toNat_of_nonneg hnonneg])

private theorem ratio_of_one_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℕ) (j : ι) (h : 4 * g j ≤ 3 * f j)
    (hrest : ∀ i, i ≠ j → g i = f i) : 4 * (∏ i, g i) ≤ 3 * (∏ i, f i) := by
  have he : (∏ i ∈ Finset.univ.erase j, g i) = ∏ i ∈ Finset.univ.erase j, f i :=
    Finset.prod_congr rfl fun i hi => hrest i (Finset.mem_erase.mp hi).1
  rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j), he,
    ← Nat.mul_assoc, ← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ h

/-- Covers the concrete determinant update used by an integer LLL implementation:
the failing pivot is replaced by the integer quotient and every other slot is retained. -/
theorem swap_interiorGramPotential {n k : ℕ} (old new : Vector ℕ (n+1))
    (hk0 : 0 < k) (hk : k < n) (a : ℤ) (ha : 0 ≤ a)
    (hfail : 4 * a < 3 * (old.get ⟨k, by omega⟩ : ℤ)^2)
    (hpivot : new.get ⟨k, by omega⟩ = (a / (old.get ⟨k, by omega⟩ : ℤ)).toNat)
    (hrest : ∀ i : Fin (n+1), i.val ≠ k → new.get i = old.get i) :
    4 * interiorGramPotential new ≤ 3 * interiorGramPotential old := by
  let row (i : Fin (n-1)) : Fin (n+1) :=
    ⟨i.val+1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))⟩
  let cut : Fin (n-1) := ⟨k-1, by omega⟩
  have hi : row cut = ⟨k, by omega⟩ := Fin.ext (by dsimp [row, cut]; omega)
  unfold interiorGramPotential
  simp only [finite_fold_mul, Nat.one_mul]
  apply ratio_of_one_factor (fun i => old.get (row i)) (fun i => new.get (row i)) cut
  · rw [hi, hpivot]
    exact (swap_quotient_four_lt_three ha hfail).le
  · intro i h
    apply hrest
    intro hi'
    apply h
    apply Fin.ext
    dsimp [row] at hi'
    dsimp [cut]
    omega

end Lattice
end LinearProgramming
end Optimization
end OAI
