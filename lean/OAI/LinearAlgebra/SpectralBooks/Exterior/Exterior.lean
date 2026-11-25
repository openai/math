import OAI.LinearAlgebra.SpectralBooks.Exterior.Signs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Creation and contraction in the ordered subset basis

The two orders of creation and contraction give the identity in the
wire-transport appendix, over any commutative ring.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Exterior

open scoped BigOperators

/-- Ordered exterior basis of degree `b` on `Q` generators. -/
abbrev Level (Q b : ℕ) := {S : Finset (Fin Q) // S.card = b}

theorem card_level (Q b : ℕ) : Fintype.card (Level Q b) = Q.choose b := by
  simp [Level, Fintype.card_finset_len]

variable (K : Type*) [CommRing K] {Q b : ℕ}

/-- Matrix of left exterior multiplication by the `i`th coordinate vector. -/
def create (i : Fin Q) : Matrix (Level Q (b + 1)) (Level Q b) K :=
  fun U S => if i ∉ S.val ∧ U.val = insert i S.val then sign K i S.val else 0

/-- Matrix of contraction with the `j`th dual coordinate vector. -/
def contract (j : Fin Q) : Matrix (Level Q b) (Level Q (b + 1)) K :=
  fun R S => if j ∈ S.val ∧ R.val = S.val.erase j then sign K j S.val else 0

private theorem contract_create_entry (i j : Fin Q) (R S : Level Q b) :
    (contract (b := b) K j * create (b := b) K i) R S =
      if i ∉ S.val ∧ j ∈ insert i S.val ∧ R.val = (insert i S.val).erase j then
        sign K i S.val * sign K j (insert i S.val) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : i ∈ S.val
  · simp [create, hi]
  let U : Level Q (b + 1) := ⟨insert i S.val, by simp [hi, S.property]⟩
  rw [Finset.sum_eq_single U]
  · dsimp [U, create, contract]
    split_ifs <;> simp_all [mul_comm]
  · intro V _ hV
    have hne : V.val ≠ insert i S.val := fun h => hV (Subtype.ext h)
    simp [create, hne]
  · simp

private theorem create_contract_entry (i j : Fin Q) (R S : Level Q (b + 1)) :
    (create (b := b) K i * contract (b := b) K j) R S =
      if j ∈ S.val ∧ i ∉ S.val.erase j ∧ R.val = insert i (S.val.erase j) then
        sign K j S.val * sign K i (S.val.erase j) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : j ∈ S.val
  · let U : Level Q b := ⟨S.val.erase j, by rw [Finset.card_erase_of_mem hj, S.property]; rfl⟩
    rw [Finset.sum_eq_single U]
    · dsimp [U, create, contract]
      split_ifs <;> simp_all [mul_comm]
    · intro V _ hV
      have hne : V.val ≠ S.val.erase j := fun h => hV (Subtype.ext h)
      simp [contract, hne]
    · simp
  · simp [contract, hj]

/-- The creation/contraction anticommutator on degree `b + 1`. Its two
summands factor through degrees `b + 2` and `b` respectively. -/
theorem anticommutator (i j : Fin Q) :
    contract K j * create K i + create K i * contract K j =
      (if i = j then 1 else 0 : Matrix (Level Q (b + 1)) (Level Q (b + 1)) K) := by
  ext R S
  rw [Matrix.add_apply, contract_create_entry, create_contract_entry]
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S.val
    · simp [hi, Finset.insert_erase hi, Matrix.one_apply,
        Subtype.ext_iff]
    · simp [hi, Finset.erase_insert hi, Matrix.one_apply,
        Subtype.ext_iff]
  · have hji := Ne.symm hij
    by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val
    all_goals simp [hij, hji, hi, hj, Finset.erase_insert_of_ne hij]
    by_cases he : R.val = insert i (S.val.erase j)
    · simpa [he] using sign_cancel K hij hi hj
    · simp [he]

/-- Splitting a marked coefficient vector into the two exterior orders
introduces a diagonal pair of basis labels. -/
theorem split_coeff (v : Fin Q → K) (i : Fin Q) (R S : Level Q (b + 1)) :
    (∑ j, (contract (b := b + 1) K j * create (b := b + 1) K i) R S * v j) +
      (∑ j, (create (b := b) K i * contract (b := b) K j) R S * v j) =
        (if R = S then 1 else 0) * v i := by
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_mul, ← Matrix.add_apply]
  simp_rw [anticommutator]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.one_apply]
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

end Exterior

end SpectralBooks
end LinearAlgebra
end OAI
