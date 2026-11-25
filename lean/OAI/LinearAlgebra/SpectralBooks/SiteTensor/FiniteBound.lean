import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Identity
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.WireProduct

/-! # Prices of the two exterior restrictions

The restriction in the tensor semiring yields an ordinary two-branch price
bound. Subtracting the wire cost from both branches leaves the differences
of the logarithms of adjacent exterior dimensions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical NNReal
open Real

namespace SiteTensor

variable {J : Type} {K : Type*} [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))

private theorem logprice_le_of_sum (X Y Z : Raw.{0} J K) (c : ℝ) (hc : 0 ≤ c)
    (hX : X.coeff ≠ 0) (hs : ofRaw X ≤ ofRaw Y + ofRaw Z) :
    rawLogPrice φ c X ≤ c + max (rawLogPrice φ c Y) (rawLogPrice φ c Z) := by
  let f (T : Raw.{0} J K) : ℝ := φ.val (ofRaw T)
  have hx : 0 < f X := by exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ X hX)
  have hnn := φ.property.2.2.2.2 _ _ hs
  rw [φ.property.2.2.1] at hnn
  have h : f X ≤ f Y + f Z := by exact_mod_cast hnn
  have branch {U : Raw.{0} J K} (hU : f X ≤ 2 * f U) : rawLogPrice φ c X ≤ c + rawLogPrice φ c U := by
    have hu : 0 < f U := by linarith
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hx hU
    rw [Real.logb_mul (by norm_num) hu.ne', Real.logb_self_eq_one (by norm_num)] at hl
    change c * logb 2 (f X) ≤ c + c * logb 2 (f U)
    linarith [mul_le_mul_of_nonneg_left hl hc]
  rcases le_total (f Y) (f Z) with h' | h'
  · exact (branch (U := Z) (by linarith)).trans (by gcongr; exact le_max_right _ _)
  · exact (branch (U := Y) (by linarith)).trans (by gcongr; exact le_max_left _ _)

omit [Fintype J] [Nonempty J] in
private theorem wire_coeff_nonzero (M : Type) [Fintype M] [Nonempty M] (p q : J) :
    (Relocation.wire K M p q).coeff ≠ 0 := by
  unfold Relocation.wire
  apply (Raw.group_ne_zero_iff ..).mpr
  intro h
  have H := congrFun h (fun _ => Classical.arbitrary M)
  change (Raw.diagonal (Fin 2) K M).coeff (fun _ => Classical.arbitrary M) = 0 at H
  simp [Raw.diagonal_coeff_at (0 : Fin 2)] at H

/-- The finite two-branch bound, for a marked tensor at three sites. The
input is the class inequality obtained by summing the two exterior restrictions. -/
theorem relocation_finite_price_bound (A B C : Raw.{0} J K)
    (hA : A.coeff ≠ 0) (hB : B.coeff ≠ 0) (hC : C.coeff ≠ 0)
    (H P M : Type) [Fintype H] [Fintype P] [Fintype M] [Nonempty H] [Nonempty P] [Nonempty M]
    (a b z : J) (u d c : ℝ) (hc : 0 ≤ c)
    (hd : rawWireDistance φ c a b = d) (hza : rawWireDistance φ c z a = u * d)
    (hzb : rawWireDistance φ c z b = (1 - u) * d)
    (h : ofRaw C * ofRaw (Relocation.wire K H a b) ≤
      (ofRaw B * ofRaw (Relocation.wire K P z b)) * ofRaw (Relocation.wire K H z a) +
      (ofRaw A * ofRaw (Relocation.wire K M z a)) * ofRaw (Relocation.wire K H z b)) :
    rawLogPrice φ c C ≤ c +
      max (rawLogPrice φ c B + ((1 - u) * d) * (logb 2 (Fintype.card P) - logb 2 (Fintype.card H)))
        (rawLogPrice φ c A + (u * d) * (logb 2 (Fintype.card M) - logb 2 (Fintype.card H))) := by
  have mul_ne (X Y : Raw.{0} J K) (hx : X.coeff ≠ 0) (hy : Y.coeff ≠ 0) : (X.mul Y).coeff ≠ 0 := by
    intro hzero
    have H := (ofRaw_eq_zero_iff (X.mul Y)).mpr hzero
    rw [ofRaw_mul] at H
    exact (mul_ne_zero ((ofRaw_eq_zero_iff X).not.mpr hx) ((ofRaw_eq_zero_iff Y).not.mpr hy)) H
  have hw (D : Type) [Fintype D] [Nonempty D] (p q : J) :
      rawLogPrice φ c (Relocation.wire K D p q) = rawWireDistance φ c p q * logb 2 (Fintype.card D) :=
    rawLogPrice_group_diagonal φ ![p,q] c
  have addwire (X : Raw.{0} J K) (hx : X.coeff ≠ 0) (D : Type) [Fintype D] [Nonempty D] (p q : J) :
      rawLogPrice φ c (X.mul (Relocation.wire K D p q)) =
        rawLogPrice φ c X + rawWireDistance φ c p q * logb 2 (Fintype.card D) := by
    rw [rawLogPrice_mul φ c _ _ hx (wire_coeff_nonzero D p q), hw]
  have hs := logprice_le_of_sum φ (C.mul (Relocation.wire K H a b))
    ((B.mul (Relocation.wire K P z b)).mul (Relocation.wire K H z a))
    ((A.mul (Relocation.wire K M z a)).mul (Relocation.wire K H z b)) c hc
    (mul_ne _ _ hC (wire_coeff_nonzero H a b)) h
  rw [addwire C hC, addwire _ (mul_ne _ _ hB (wire_coeff_nonzero P z b)),
    addwire _ (mul_ne _ _ hA (wire_coeff_nonzero M z a)), addwire B hB, addwire A hA,
    hd, hza, hzb] at hs
  rw [← sub_le_iff_le_add']
  apply le_trans (b := max _ _ - d * logb 2 (Fintype.card H))
  · linarith only [hs]
  rw [sub_eq_add_neg, ← max_add_add_right]
  apply max_le_max <;> apply le_of_eq <;> ring

namespace Relocation

open Exterior

/-- The two exterior-algebra factorizations give the finite price inequality
for every valid level `b + 1`, allowing coincident sites and zero summands. -/
theorem marked_finite_price_bound {I : Type} [Fintype I] {A : I → Type} [∀ i, Fintype (A i)]
    {Q b : ℕ} (hb : b + 2 ≤ Q) (T : (∀ i, A i) → Fin Q → K)
    (hT : (marked A (Fin Q) T).coeff ≠ 0) (σ : I → J) (a z e : J)
    (u d c : ℝ) (hc : 0 ≤ c) (hd : rawWireDistance φ c a e = d)
    (hza : rawWireDistance φ c z a = u * d) (hze : rawWireDistance φ c z e = (1 - u) * d) :
    rawLogPrice φ c ((marked A (Fin Q) T).group (placeMark σ z)) ≤ c +
      max (rawLogPrice φ c ((marked A (Fin Q) T).group (placeMark σ e)) +
            ((1 - u) * d) * (logb 2 (Q.choose (b+2)) - logb 2 (Q.choose (b+1))))
          (rawLogPrice φ c ((marked A (Fin Q) T).group (placeMark σ a)) +
            (u * d) * (logb 2 (Q.choose b) - logb 2 (Q.choose (b+1)))) := by
  have nz (k : ℕ) (hk : k ≤ Q) : Nonempty (Level Q k) :=
    Fintype.card_pos_iff.mp (by rw [card_level]; exact Nat.choose_pos hk)
  have := nz b (by omega)
  have := nz (b+1) (by omega)
  have := nz (b+2) hb
  have hsplit := grouped_split_le (b := b) T σ z a e
  have hprod := grouped_split_eq_mul T (Level Q (b+1)) σ z a e
  have hclass := hprod.symm.le.trans <| hsplit.trans (add_mono
    (ofRaw_le_iff.mpr (plus_restricts T (create K) (contract K) σ z a e))
    (ofRaw_le_iff.mpr (minus_restricts T (contract K) (create K) σ z a e)))
  have nth (p : J) := ((marked A (Fin Q) T).group_ne_zero_iff (placeMark σ p)).mpr hT
  simpa only [card_level] using relocation_finite_price_bound φ _ _ _ (nth a) (nth e) (nth z)
    (Level Q (b+1)) (Level Q (b+2)) (Level Q b) a e z u d c hc hd hza hze hclass

end Relocation
end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
