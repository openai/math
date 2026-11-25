import OAI.LinearAlgebra.FiniteFourier.Transform
import OAI.LinearAlgebra.FiniteFourier.CircuitReindex
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # The cyclic discrete Fourier transform

A primitive root orders the characters of `ZMod n` by frequencies in `Fin n`.
In that order the character transform and its inverse give the usual DFT matrices.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] {ζ : K}

/-- A primitive root of order `n` gives the manuscript's splitting hypothesis for `ZMod n`. -/
theorem admissible_zmod (hζ : IsPrimitiveRoot ζ n) : Admissible (ZMod n) K := by
  rw [Admissible, ZMod.card, ZMod.exponent]
  exact ⟨hζ.neZero'.out, ζ, hζ⟩

private noncomputable def cyclicCharacter (hζ : IsPrimitiveRoot ζ n) (j : Fin n) :
    Character (ZMod n) K :=
  (AddChar.zmodChar n ((mem_rootsOfUnity n hζ.toRootsOfUnity.val).mp
    hζ.toRootsOfUnity.property)).toMonoidHom ^ j.val

private theorem cyclicCharacter_natCast (hζ : IsPrimitiveRoot ζ n) (j : Fin n) (a : ℕ) :
    (cyclicCharacter hζ j (Multiplicative.ofAdd (a : ZMod n)) : K) = ζ ^ (j.val * a) := by
  simp only [cyclicCharacter, MonoidHom.pow_apply, AddChar.toMonoidHom_apply,
    toAdd_ofAdd, AddChar.zmodChar_apply', Units.val_pow_eq_pow_val,
    hζ.val_toRootsOfUnity_coe, ← pow_mul, Nat.mul_comm a j.val]

/-- Frequency `j` indexes the character `g ↦ ζ^(j*g)`. -/
noncomputable def cyclicCharacterEquiv (hζ : IsPrimitiveRoot ζ n) :
    Fin n ≃ Character (ZMod n) K :=
  Equiv.ofBijective (cyclicCharacter hζ) <|
    (Fintype.bijective_iff_injective_and_card _).2 ⟨by
      intro i j hij
      have he := congrArg (fun χ : Character (ZMod n) K =>
        (χ (Multiplicative.ofAdd ((1 : ℕ) : ZMod n)) : K)) hij
      rw [cyclicCharacter_natCast, cyclicCharacter_natCast, Nat.mul_one, Nat.mul_one] at he
      exact Fin.ext (hζ.pow_inj i.isLt j.isLt he), by
      rw [Fintype.card_fin, card_character _ _ (admissible_zmod hζ), ZMod.card]⟩

private theorem finEquiv_eq_natCast (i : Fin n) :
    ZMod.finEquiv n i = (i.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => exact (ZMod.natCast_zmod_val (n := m + 1) i).symm

/-- The positive-sign Fourier matrix of order `n`, in the chosen primitive root. -/
def dftMatrix {R : Type*} [Monoid R] (n : ℕ) (ζ : R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun j a => ζ ^ (j.val * a.val)

/-- The inverse DFT, whose entries use inverse roots and the free normalization `1/n`. -/
noncomputable def inverseDftMatrix (n : ℕ) (ζ : K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a j => (n : K)⁻¹ * (ζ ^ (j.val * a.val))⁻¹

theorem reindex_fourierMatrix_zmod (hζ : IsPrimitiveRoot ζ n) :
    Matrix.reindex (cyclicCharacterEquiv hζ).symm (ZMod.finEquiv n).toEquiv.symm
      (fourierMatrix (ZMod n) K) = dftMatrix n ζ := by
  ext j a
  change (cyclicCharacter hζ j (Multiplicative.ofAdd (ZMod.finEquiv n a)) : K) = _
  rw [finEquiv_eq_natCast, cyclicCharacter_natCast]
  rfl

theorem reindex_inverseFourierMatrix_zmod (hζ : IsPrimitiveRoot ζ n) :
    Matrix.reindex (ZMod.finEquiv n).toEquiv.symm (cyclicCharacterEquiv hζ).symm
      (inverseFourierMatrix (ZMod n) K) = inverseDftMatrix n ζ := by
  ext a j
  change (Fintype.card (ZMod n) : K)⁻¹ *
    ((cyclicCharacter hζ j) (Multiplicative.ofAdd (ZMod.finEquiv n a))⁻¹ : Kˣ) = _
  rw [ZMod.card, map_inv, Units.val_inv_eq_inv_val, finEquiv_eq_natCast, cyclicCharacter_natCast]
  rfl

/-- Replacing the character indices by cyclic frequencies preserves exact circuit size. -/
theorem complexity_dftMatrix (hζ : IsPrimitiveRoot ζ n) :
    complexity (dftMatrix n ζ) = complexity (fourierMatrix (ZMod n) K) := by
  rw [← reindex_fourierMatrix_zmod hζ, complexity_reindex]

/-- The inverse DFT has exactly the circuit size of the inverse character transform. -/
theorem complexity_inverseDftMatrix (hζ : IsPrimitiveRoot ζ n) :
    complexity (inverseDftMatrix n ζ) = complexity (inverseFourierMatrix (ZMod n) K) := by
  rw [← reindex_inverseFourierMatrix_zmod hζ, complexity_reindex]

end FiniteFourier
end LinearAlgebra
end OAI
