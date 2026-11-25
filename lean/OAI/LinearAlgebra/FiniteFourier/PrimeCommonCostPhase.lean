import OAI.LinearAlgebra.FiniteFourier.PrimeDigits
import OAI.LinearAlgebra.FiniteFourier.PrimeQueryTuple

/-! # Packing the charged common kernel into ordinary Fourier digits

An invertible scalar on the query changes the two chirp phases and permutes
the output digits. All `2 * D` active axes can use the same positive-sign
Fourier transform.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

abbrev PrimeCommonPair (ℓ f D : ℕ) :=
  (Fin f → Fin D → ZMod ℓ) × (Fin f → Fin D → ZMod ℓ)

private def commonPosition (D f : ℕ) :
    Fin f × (Fin D ⊕ Fin D) ≃ Fin ((2 * D) * f) :=
  (Equiv.prodComm _ _).trans
    (((finSumFinEquiv.trans (finCongr (two_mul D).symm)).prodCongr (Equiv.refl _)).trans
      finProdFinEquiv)

private def commonDigits {ℓ f D : ℕ} : PrimeCommonPair ℓ f D ≃
    (Fin f × (Fin D ⊕ Fin D) → ZMod ℓ) where
  toFun x p := Sum.elim (x.1 p.1) (x.2 p.1) p.2
  invFun x := (fun c d => x (c, .inl d), fun c d => x (c, .inr d))
  left_inv _ := rfl
  right_inv x := by funext ⟨c,d⟩; cases d <;> rfl

/-- Pack both common tuples into a single Fourier word. -/
def primeCommonPack {ℓ f D : ℕ} [NeZero ℓ] :
    PrimeCommonPair ℓ f D ≃ (Fin ((2*D)*f) → Fin ℓ) :=
  commonDigits.trans ((commonPosition D f).arrowCongr (ZMod.finEquiv ℓ).toEquiv.symm)

/-- Multiplying both halves by a unit and interchanging them is a permutation. -/
def primeCommonSwapScale {ℓ f D : ℕ} (a : (ZMod ℓ)ˣ) :
    PrimeCommonPair ℓ f D ≃ PrimeCommonPair ℓ f D where
  toFun x := (fun c d => a * x.2 c d, fun c d => a * x.1 c d)
  invFun x := (fun c d => ↑(a⁻¹) * x.2 c d, fun c d => ↑(a⁻¹) * x.1 c d)
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]

private theorem commonDigit_val {ℓ : ℕ} [NeZero ℓ] (x : ZMod ℓ) :
    ((ZMod.finEquiv ℓ).symm x).val = x.val := by
  cases ℓ with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ ℓ => rfl

variable {ℓ f D : ℕ} [NeZero ℓ] {K : Type*} [CommRing K] {ζ : K}

/-- The packed transform is the product of the Fourier phases on both tuples. -/
theorem primeTransform_commonPack (hζ : IsPrimitiveRoot ζ ℓ) (o i : PrimeCommonPair ℓ f D) :
    primeTransform ℓ ((2*D)*f) ζ (primeCommonPack o) (primeCommonPack i) =
      digitPhase hζ (∑ c, ((∑ d, o.1 c d * i.1 c d) + ∑ d, o.2 c d * i.2 c d)) := by
  let e := commonPosition D f
  have hsum : (∑ p : Fin f × (Fin D ⊕ Fin D), commonDigits o p * commonDigits i p) =
      ∑ c, ((∑ d, o.1 c d * i.1 c d) + ∑ d, o.2 c d * i.2 c d) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun c _ => Fintype.sum_sum_type _
  rw [← hsum, digitPhase_sum, primeTransform_apply, ← e.prod_comp]
  apply Finset.prod_congr rfl
  intro p _
  change ζ ^ (((ZMod.finEquiv ℓ).symm (commonDigits o (e.symm (e p)))).val *
      ((ZMod.finEquiv ℓ).symm (commonDigits i (e.symm (e p)))).val) = _
  simp only [Equiv.symm_apply_apply, commonDigit_val, digitPhase_apply, ZMod.val_mul,
    hζ.eq_orderOf, pow_mod_orderOf]

/-- The per-row diagonal in the chirped common transform. -/
def primeCommonChirp (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ) (x : PrimeCommonPair ℓ f D) : K :=
  digitPhase hζ (∑ c, ∑ d, -(↑(a⁻¹) * x.1 c d * x.2 c d))

/-- A quadratic difference kernel is a scaled, chirped and permuted Fourier matrix. -/
theorem primeCommonChirp_factor (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ)
    (o i : PrimeCommonPair ℓ f D) :
    digitPhase hζ (↑(a⁻¹) * ∑ c, ∑ d, (i.1 c d - o.1 c d) * (o.2 c d - i.2 c d)) =
      primeCommonChirp hζ a o * (primeCommonChirp hζ a i *
        primeTransform ℓ ((2*D)*f) ζ (primeCommonPack (primeCommonSwapScale a⁻¹ o))
          (primeCommonPack i)) := by
  rw [primeTransform_commonPack hζ]
  unfold primeCommonChirp
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, primeCommonSwapScale, Equiv.coe_fn_mk]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

end

end

end FiniteFourier
end LinearAlgebra
end OAI
