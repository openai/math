import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! # Pascal minors in the integral fermion pairing -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Matrix Finset

/-- Minor on increasing lists of occupied modes, extended by zero when the
lists have different cardinalities. -/
noncomputable def stateMinor (f : ℕ → ℕ → ℤ) (I J : Finset ℕ) : ℤ :=
  if h : J.card = I.card then
    (Matrix.of fun i j : Fin I.card ↦ f (I.orderEmbOfFin rfl i) (J.orderEmbOfFin h j)).det
  else 0

/-- Exterior minor of the lower-triangular Pascal matrix. -/
noncomputable def pascalMinor := stateMinor (fun i j ↦ (i.choose j : ℤ))

/-- Sign contributed by interleaving the fermions and differentiating the
first field of each contracted pair. -/
def pairingSign (I : Finset ℕ) : ℤ := (-1) ^ (I.card.choose 2 + ∑ i ∈ I, i)

/-- Integral coefficient of the fully contracted fermion fields. -/
noncomputable def pairing (I J : Finset ℕ) : ℤ :=
  pairingSign I * stateMinor (fun i j ↦ ((i+j).choose i : ℤ)) I J

/-- The scalar product of two truncated Pascal rows is the symmetric
binomial coefficient of their indices. -/
theorem pascal_gram_entry {N i j : ℕ} (hi : i < N) :
    (∑ k ∈ range N, (i.choose k : ℤ) * (j.choose k : ℤ)) = ((i + j).choose i : ℤ) := by
  have hN : (∑ k ∈ range N, i.choose k * j.choose k) =
      ∑ k ∈ range (i+1), i.choose k * j.choose k := by
    symm
    apply sum_subset_zero_on_sdiff (range_mono hi) <;> simp_all [Nat.choose_eq_zero_of_lt]
  exact_mod_cast hN.trans (by
    rw [Nat.add_comm i j, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply sum_congr rfl
    intro k hk
    rw [Nat.choose_symm (mem_range_succ_iff.mp hk), mul_comm])

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
