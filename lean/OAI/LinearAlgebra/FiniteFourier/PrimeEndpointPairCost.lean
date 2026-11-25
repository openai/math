import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointCost
import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointSplit
import OAI.LinearAlgebra.FiniteFourier.PrimeCommonCostPhase

/-! # The cost of the two-half Fourier endpoint

Pairing both halves with their dual coordinates is a Fourier transform on twice
as many axes. Multiplication by the inverse query power relabels the frequencies.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
open scoped Classical

variable {ℓ f h F : ℕ} [NeZero ℓ] {K : Type*} [CommRing K] {ζ : K}

/-- Fourier matrix of the restricted pairing, with character frequencies expressed
in the dual coordinates of both halves. -/
def endpointPairFourier (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ) :
    Matrix (PrimeCommonPair ℓ f h) (PrimeCommonPair ℓ f h) K :=
  fun q x => digitPhase hζ (↑(a⁻¹) *
    ∑ c, ∑ i, (x.1 c i * q.1 c i + x.2 c i * q.2 c i))

/-- In each of the `h` active coordinates of both halves, perform one transform
over all `f` columns. The spectators may use any indexing set of the requisite
size. The query power only permutes frequency labels. -/
theorem primeTemplate_endpointPairFourier (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ)
    (S : Type) [Fintype S] (hF : 0 < 2 * h → ℓ ^ ((2 * h - 1) * f) * Fintype.card S = F) :
    PrimeTemplateProgram ℓ f F ζ (endpointPartial (endpointPairFourier (f := f) (h := h) hζ a) S)
      0 (2 * h) := by
  let e := (primeCommonPack (ℓ := ℓ) (f := f) (D := h)).prodCongr (Equiv.refl S)
  let b := (primeCommonSwapScale (f := f) (D := h) a⁻¹).trans (Equiv.prodComm _ _)
  let u := (b.prodCongr (Equiv.refl S)).trans e
  have prog := (primeTemplate_partialTransform ζ (2 * h) S hF).reindex u.symm e.symm
  convert prog using 1
  ext ⟨q,n⟩ ⟨x,m⟩
  change (if m = n then endpointPairFourier hζ a q x else 0) =
    Matrix.blockDiagonal (fun _ : S => primeTransform ℓ ((2*h)*f) ζ)
      (primeCommonPack (b q), n) (primeCommonPack x, m)
  by_cases hm : m = n
  · subst n
    rw [ite_eq_left rfl, Matrix.blockDiagonal_apply_eq, primeTransform_commonPack hζ]
    unfold endpointPairFourier
    congr 1
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, b, primeCommonSwapScale,
      Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.prodComm_apply, Prod.swap_prod_mk]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
  · simp [hm, Ne.symm hm, Matrix.blockDiagonal_apply]

/-- Recover the number of fibers of one axis from the total row volume. -/
theorem prime_axisFiberCount_of_volume {A d ℓ f n : ℕ} (hℓ : 0 < ℓ)
    (hA : 0 < A) (hd : 0 < d) (hvol : ℓ ^ (d*f) * n = ℓ ^ (A*f)) :
    ℓ ^ ((d-1)*f) * n = ℓ ^ ((A-1)*f) := by
  apply Nat.eq_of_mul_eq_mul_left (show 0 < ℓ ^ f from pow_pos hℓ _)
  rw [← Nat.mul_assoc, ← pow_add, ← pow_add]
  have hexp (k : ℕ) (hk : 0 < k) : f + (k-1)*f = k*f := by
    calc
      f + (k-1)*f = (1+(k-1))*f := by ring
      _ = k*f := by rw [show 1 + (k-1) = k by omega]
  simpa only [hexp d hd, hexp A hA] using hvol

/-- The endpoint has the required fiber count whenever its input chart is a
bijection to a full row of the declared volume. -/
theorem primeTemplate_endpointPairFourier_of_chart {A : ℕ} (hA : 0 < A)
    (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ) (S V : Type) [Fintype S] [Fintype V]
    (e : V ≃ PrimeCommonPair ℓ f h × S) (hvol : Fintype.card V = ℓ ^ (A*f)) :
    PrimeTemplateProgram ℓ f (ℓ ^ ((A-1)*f)) ζ
      (endpointPartial (endpointPairFourier (f := f) (h := h) hζ a) S) 0 (2 * h) := by
  apply primeTemplate_endpointPairFourier hζ a
  intro hd
  apply prime_axisFiberCount_of_volume (Nat.pos_of_ne_zero (NeZero.ne ℓ)) hA hd
  have hc : Fintype.card (PrimeCommonPair ℓ f h) = ℓ ^ ((2*h)*f) := by
    simpa using Fintype.card_congr (primeCommonPack (ℓ := ℓ) (f := f) (D := h))
  simpa only [Fintype.card_prod, hc] using (Fintype.card_congr e).symm.trans hvol

end

end FiniteFourier
end LinearAlgebra
end OAI
