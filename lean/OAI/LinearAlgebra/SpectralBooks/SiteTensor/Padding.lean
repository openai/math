import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Push
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Nonzero

/-! # A uniform dyadic format for finite-site tensors

Padding each local basis by zeros allows every moving mark to have the same
power-of-two dimension. The projection back to the original coordinates is
a local restriction even when some local basis, or the site set, is empty.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

variable {I : Type*} [Fintype I] {K : Type*} [CommSemiring K]

/-- Mutual restriction preserves nonvanishing, including for empty site sets. -/
theorem Equivalent.coeff_ne_zero_iff {T U : Raw I K} (h : T.Equivalent U) :
    T.coeff ≠ 0 ↔ U.coeff ≠ 0 := by
  apply not_congr
  rw [← ofRaw_eq_zero_iff T, ← ofRaw_eq_zero_iff U, ofRaw_eq_iff.mpr h]

/-- Embed every local basis into a common dyadic index set and pad by zeros.
The exponent is positive, even for a tensor with no sites. -/
theorem exists_dyadic_padding (T : Raw.{0} I K) :
    ∃ k : ℕ, 0 < k ∧ ∃ U : Raw.{0} I K,
      (∀ i, Fintype.card (U.Leg i) = 2 ^ k) ∧ T.Equivalent U := by
  classical
  let d := Finset.univ.sup (fun i => Fintype.card (T.Leg i))
  let k := d + 1
  have hd (i : I) : Fintype.card (T.Leg i) ≤ d :=
    Finset.le_sup (f := fun i => Fintype.card (T.Leg i)) (Finset.mem_univ i)
  let e (i : I) : T.Leg i ↪ Fin (2 ^ k) :=
    (Fintype.equivFin (T.Leg i)).toEmbedding.trans
      (Fin.castLEEmb ((hd i).trans ((Nat.le_succ d).trans k.lt_two_pow_self.le)))
  let U : Raw.{0} I K := ⟨fun _ => Fin (2 ^ k), fun _ => inferInstance,
    pushCoeff (fun x i => e i (x i)) T.coeff⟩
  exact ⟨k, Nat.succ_pos _, U, fun _ => Fintype.card_fin _, equivalent_pushCoeff e T.coeff⟩

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
