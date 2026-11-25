import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import OAI.LinearAlgebra.SpectralBooks.ConcreteSpectrum
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal
import OAI.LinearAlgebra.SpectralBooks.TrivialSlotsAdd
import OAI.LinearAlgebra.SpectralBooks.PartialDiagonal
import OAI.LinearAlgebra.SpectralBooks.SubadditiveSpectralBound

/-! # Ordinary sums priced by the diagonal of their support

Adjoining trivial slots preserves tensor products. A direct sum formed only
on the occupied sites restricts from the ambient direct sum. The induced
multiplicative evaluation is therefore subadditive. The polynomially many
multinomial profiles in high powers turn this subadditivity into the sharp
logarithmic cost involving the binary diagonal on the occupied sites.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped BigOperators NNReal

namespace SiteTensor

universe v
variable {S O K : Type*} [Fintype S] [Fintype O] [Nonempty S] [CommSemiring K]

/-- Append scalar slots to each representative of a tensor class. -/
def withTrivialHom (O : Type*) [Fintype O] :
    TensorClass.{v} S K →* TensorClass.{v} (S ⊕ O) K where
  toFun := Quotient.map (Raw.withTrivial O) (fun _ _ h =>
    ⟨Raw.withTrivial_restricts O h.1, Raw.withTrivial_restricts O h.2⟩)
  map_one' := ofRaw_eq_iff.mpr (Raw.withTrivial_one_equivalent O)
  map_mul' X Y := Quotient.inductionOn₂ X Y fun x y =>
    ofRaw_eq_iff.mpr (Raw.withTrivial_mul_equivalent O x y)

theorem withTrivialHom_mono : Monotone (withTrivialHom (S := S) (K := K) O) := by
  intro X Y
  exact Quotient.inductionOn₂ X Y (fun _ _ => Raw.withTrivial_restricts O)

theorem withTrivialHom_add_le (X Y : TensorClass.{v} S K) :
    withTrivialHom O (X + Y) ≤ withTrivialHom O X + withTrivialHom O Y :=
  Quotient.inductionOn₂ X Y (Raw.withTrivial_add_restricts O)

@[simp] theorem withTrivialHom_zero :
    withTrivialHom O (0 : TensorClass.{v} S K) = 0 :=
  (ofRaw_eq_zero_iff _).mpr rfl

/-- The natural number in the smaller semiring becomes the corresponding
diagonal on the occupied sites in the ambient semiring. -/
theorem withTrivialHom_natCast (n : ℕ) :
    withTrivialHom O (n : TensorClass.{0} S K) = supportDiagonalHom S O K n := by
  rw [← ofRaw_diagonal_fin_eq_natCast S K n]
  rfl

section Field
variable {F : Type*} [Field F]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (S ⊕ O) F → _ → Prop))
variable {A : S → Type} [∀ s, Fintype (A s)]

/-- Equation `price-ordinary` for an ambient point on `S ⊔ O` evaluated on
tensors supported on `S`. The coefficient of `log₂ |J|` is the same price
evaluated at the binary diagonal supported on `S`. -/
theorem subset_ordinary_sum_logb_le {J : Type*} [Fintype J] (T : J → (∀ s, A s) → F)
    (hsum : ∑ j, T j ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    let H := fun X : TensorClass.{0} (S ⊕ O) F => c * Real.logb 2 (φ.val X)
    ∃ j, T j ≠ 0 ∧ H (withTrivialHom O (ofCoeffs (∑ k, T k))) ≤
      H (withTrivialHom O (ofCoeffs (T j))) +
        H (ofRaw (Raw.supportDiagonal S O F (Fin 2))) * Real.logb 2 (Fintype.card J) := by
  classical
  cases isEmpty_or_nonempty J with
  | inl _ => simp at hsum
  | inr _ =>
    let v := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (withTrivialHom (S := S) O)
    have hmono : Monotone v := fun _ _ h => φ.2.2.2.2.2 _ _ (withTrivialHom_mono h)
    have hadd (x y : TensorClass.{0} S F) : v (x + y) ≤ v x + v y := by
      change φ.val (withTrivialHom O (x + y)) ≤ _
      exact (φ.2.2.2.2.2 _ _ (withTrivialHom_add_le x y)).trans_eq (φ.2.2.2.1 _ _)
    have hnat {a b : ℕ} (_ : 0 < a) (h : a ≤ b) : v (a : TensorClass.{0} S F) ≤ v b := by
      change φ.val (withTrivialHom O _) ≤ φ.val (withTrivialHom O _)
      rw [withTrivialHom_natCast, withTrivialHom_natCast]
      exact φ.2.2.2.2.2 _ _ (supportDiagonalHom_mono S O F h)
    have hpos : 0 < v (ofCoeffs (∑ j, T j)) := by
      have h := hmono (show (1 : TensorClass.{0} S F) ≤ ofCoeffs (∑ j, T j) from
        ofRaw_le_iff.mpr (Crossing.unit_restricts_of_nonzero hsum))
      exact zero_lt_one.trans_le ((map_one v) ▸ h)
    have hs := hmono (ordinary_sum_le T)
    obtain ⟨j, hj, hbound⟩ := subadditiveSpectral_exists_logb_summand v
      (spectral_natCast_logb_nonneg v hnat 2 (by norm_num)) hadd
      (fun n hn => (spectral_natCast_eq_rpow v hnat n hn).le) (fun k => ofCoeffs (T k)) (hpos.trans_le hs)
    have hbj := (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hpos) (by exact_mod_cast hs)).trans hbound
    have hdiag : v ((2 : ℕ) : TensorClass S F) = φ.val (ofRaw (Raw.supportDiagonal S O F (Fin 2))) :=
      congrArg φ.val (withTrivialHom_natCast (S := S) (O := O) (K := F) 2)
    rw [hdiag] at hbj
    refine ⟨j, ?_, ?_⟩
    · intro hz
      rw [hz, ofCoeffs_zero] at hj
      have hv0 : v 0 = 0 := (congrArg φ.val withTrivialHom_zero).trans φ.2.1
      simp [hv0] at hj
    · exact (mul_le_mul_of_nonneg_left hbj hc).trans_eq (by rw [mul_add, ← mul_assoc]; rfl)

/-- A zero price for the binary support diagonal forces the price of every
tensor on the support to vanish, since each tensor is bounded by a finite
diagonal. -/
theorem subset_log_price_eq_zero_of_diagonal
    (hδ : Real.logb 2 (φ.val (ofRaw (Raw.supportDiagonal S O F (Fin 2)))) = 0)
    (X : TensorClass.{0} S F) :
    Real.logb 2 (φ.val (withTrivialHom O X)) = 0 := by
  by_cases hx : X = 0
  · simp [hx, φ.property.1]
  obtain ⟨n, hn⟩ := exists_le_natCast X
  have hn' : 0 < n := by
    by_contra! h
    have h0 : n = 0 := by omega
    exact hx (le_antisymm (by simpa [h0] using hn) (zero_le_tensor _))
  have hlow := φ.property.2.2.2.2 _ _ (withTrivialHom_mono (O := O) (one_le_of_ne_zero hx))
  simp only [map_one, φ.property.2.1] at hlow
  have hhi := φ.property.2.2.2.2 _ _ (withTrivialHom_mono (O := O) hn)
  rw [withTrivialHom_natCast] at hhi
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast zero_lt_one.trans_le hlow) (by exact_mod_cast hhi)
  have hd := supportDiagonal_log_price S O F φ hn'
  rw [hδ, zero_mul] at hd
  exact le_antisymm (hlog.trans_eq hd) (Real.logb_nonneg (by norm_num) (by exact_mod_cast hlow))

end Field
end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
