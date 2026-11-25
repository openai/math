import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicDeformationCircuits

/-! # The two coordinate transforms for multiplication on one active sector -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation.Dyadic

open Polynomial Matrix
open scoped BigOperators

variable {R S σ : Type*} [CommRing R] [CommRing S] [Fintype σ] [DecidableEq σ]
  {φ : R →+* S} {η : S} {M : S[X]} {e r s H : ℕ}

/-- The Fourier words and lifted generator scalings give a pair of circuits
which recover the sector product from the products at its split points. -/
theorem exists_productStages (m : σ → ℕ) (β : σ → (AdjoinRoot M)ˣ)
    (hm : ∀ i, IsUnit (m i : AdjoinRoot M))
    (w : σ → (AdjoinRoot M)ˣ) (hw : ∀ i, w i ^ m i = 1)
    (hs : ∀ i, Pairwise fun j k : Fin (m i) =>
      IsUnit ((w i : AdjoinRoot M)^j.val - (w i : AdjoinRoot M)^k.val))
    (basis : Function.Bijective (fun x : Fin 2 → R => φ (x 0) + η * φ (x 1)))
    (hM : M.Monic) (hd : M.natDegree = e) (he : 0 < e) (hr : 0 < r)
    (jets : ∀ t : ℕ, 0 < t → JetCircuitsOver φ η M e t)
    (height : H = 2*r+Fintype.card σ) (hc : 2*e*H ≤ s) {Cf Cb : ℝ}
    (hF : JetMatrixCircuit φ η M e H
      ((evaluation m (fun i j => (w i : AdjoinRoot M)^j.val)).map
        (algebraMap (AdjoinRoot M) (JetQuotient M H))) Cf)
    (hI : JetMatrixCircuit φ η M e H
      ((interpolation m (fun i j => (w i : AdjoinRoot M)^j.val)).map
        (algebraMap (AdjoinRoot M) (JetQuotient M H))) Cb) :
    ∃ (f : (Address m → JetQuotient M r) → (Address m → JetQuotient M H))
      (g : (Address m → JetQuotient M H) → (Address m → JetQuotient M r)),
      JetStage φ η M e r H f (Cf+endpointCost (Fintype.card (Address m)) e r H s) ∧
      JetStage φ η M e H r g (Cb+endpointCost (Fintype.card (Address m)) e H r s) ∧
      ∀ x y, g (f x * f y) = multiply
        (coeff (fun i => algebraMap (AdjoinRoot M) (JetQuotient M r) (β i : AdjoinRoot M)) m) x y := by
  subst H
  let H := 2*r+Fintype.card σ
  let ζ (i : σ) (j : Fin (m i)) := (w i : AdjoinRoot M)^j.val
  have hζ (i : σ) (j : Fin (m i)) : ζ i j ^ m i = 1 := by
    have h := congrArg (fun u : (AdjoinRoot M)ˣ => (u : AdjoinRoot M)) (hw i)
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h
    rw [show ζ i j = (w i : AdjoinRoot M)^j.val from rfl, ← pow_mul, Nat.mul_comm j.val, pow_mul, h, one_pow]
  obtain ⟨u,v,huv⟩ := split_product r hr m β hm ζ hζ hs
  have hH : 0 < H := by dsimp [H]; omega
  have hcr : 2*e*r ≤ s := (Nat.mul_le_mul_left (2*e) (by omega : r ≤ H)).trans hc
  exact ⟨_, _, transformInput_stage m u v ζ (jets r hr) (jets H hH) basis hM hd he hr hH hcr hc hF,
    transformOutput_stage m u v ζ (jets r hr) (jets H hH) basis hM hd he hr hH hcr hc hI, huv⟩

end Deformation.Dyadic

end FiniteFourier
end LinearAlgebra
end OAI
