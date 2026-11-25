import OAI.LinearAlgebra.SpectralBooks.SpectralPlacementPrices.ShortenPrice
import OAI.LinearAlgebra.SpectralBooks.SpectralSublevels

namespace OAI
/-! # Selecting a summand at a fixed placement

The fixed tensor format is preserved when passing to the closure of the sums.
The summand can therefore be selected from an actual decomposition before
choosing any cut of its legs. Repeated and coincident sites are allowed. -/

namespace Hierarchy.ForceSelection

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators

variable {F : Type*} [Field F] {I : Type} [Fintype I] [Nonempty I]
  {A : I → Type} [∀ i, Fintype (A i)] {J : Type*} [Fintype J]

/-- The raw tensor associated to coefficients in the fixed format. -/
abbrev raw (t : (∀ i, A i) → F) : Raw.{0} I F := ⟨A, inferInstance, t⟩

omit [Fintype I] [Nonempty I] [∀ i, Fintype (A i)] in
/-- Some coefficient of an actual summand is nonzero if the closure of all
sums contains a nonzero tensor. This also covers a collapsed placement. -/
private theorem exists_nonzero {S : Set (J → (∀ i, A i) → F)} {t : (∀ i, A i) → F}
    (ht : t ∈ affineZariskiClosure ((fun Y => ∑ j, Y j) '' S)) (ht0 : t ≠ 0) :
    ∃ Y ∈ S, ∃ j, Y j ≠ 0 := by
  classical
  by_contra! h
  apply ht0
  funext a
  have hz := ht (MvPolynomial.X a) (by
    rintro _ ⟨Y,hY,rfl⟩
    simp [h Y hY])
  simpa using hz

/-- At any placement there is a nonzero summand in an actual decomposition whose
price is within the ordinary-sum loss and an arbitrary positive tolerance of the
target price, including when the target belongs only to the Zariski closure.
The number of slots can exceed the number of nonzero summands. -/
theorem exists_summand {E : Type*} [MetricSpace E] (P : SpectralPlacementPrices F E)
    (x : I → E) {S : Set (J → (∀ i, A i) → F)} {t : (∀ i, A i) → F}
    (ht : t ∈ affineZariskiClosure ((fun Y => ∑ j, Y j) '' S)) (ht0 : t ≠ 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ Y ∈ S, ∃ j, Y j ≠ 0 ∧
      P.price (raw t) x - ε - P.price (Raw.diagonal I F (Fin 2)) x *
          Real.logb 2 (Fintype.card J) < P.price (raw (Y j)) x := by
  classical
  rcases P.all_zero_or_normalized_at x with hprice | ⟨φ,c,hc,hprice⟩
  · obtain ⟨Y,hY,j,hj⟩ := exists_nonzero ht ht0
    refine ⟨Y,hY,j,hj,?_⟩
    simp only [hprice,zero_mul,sub_zero,zero_sub]
    linarith
  have price (z : (∀ i, A i) → F) :
      P.price (raw z) x = c * Real.logb 2 (coeffValue φ z : ℝ) := by
    exact hprice (raw z)
  have delta : P.price (Raw.diagonal I F (Fin 2)) x = c := by
    have he := map_natCast (normalizedSpectrum.toRingHom φ) 2
    change φ.val (2 : TensorClass.{0} I F) = 2 at he
    simp [hprice,rawLogPrice,he]
  obtain ⟨Y,hY,hne,hnear⟩ : ∃ Y ∈ S, (∑ j, Y j) ≠ 0 ∧
      P.price (raw t) x - ε < P.price (raw (∑ j, Y j)) x := by
    by_contra! hall
    have hle := logPrice_le_of_mem_closure φ ht ht0 hc.le (b := P.price (raw t) x - ε)
      (by
        rintro _ ⟨Y,hY,rfl⟩ hY0
        rw [← price]
        exact hall Y hY hY0)
    rw [← price] at hle
    linarith
  obtain ⟨j,hj,upper⟩ := ordinary_sum_logb_le φ Y hne hc.le
  refine ⟨Y,hY,j,hj,?_⟩
  rw [delta,price,price]
  rw [price,price] at hnear
  linarith

/-- If every attainable tensor admits a bounded decomposition satisfying a
joint property, the selected summand belongs to one such decomposition of an
attainable tensor. In particular its cut constraints hold for the same witness. -/
theorem exists_summand_of_decompositions {E : Type*} [MetricSpace E]
    (P : SpectralPlacementPrices F E) (x : I → E)
    {D : Set ((∀ i, A i) → F)} {t : (∀ i, A i) → F}
    (ht : t ∈ affineZariskiClosure D) (ht0 : t ≠ 0)
    (Q : (J → (∀ i, A i) → F) → Prop)
    (hD : ∀ z ∈ D, ∃ Y, (∑ j, Y j) = z ∧ Q Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y, (∑ j, Y j) ∈ D ∧ Q Y ∧ ∃ j, Y j ≠ 0 ∧
      P.price (raw t) x - ε - P.price (Raw.diagonal I F (Fin 2)) x *
        Real.logb 2 (Fintype.card J) < P.price (raw (Y j)) x := by
  let S := {Y : J → (∀ i, A i) → F | (∑ j, Y j) ∈ D ∧ Q Y}
  have hcl : t ∈ affineZariskiClosure ((fun Y => ∑ j, Y j) '' S) := by
    intro p hp
    apply ht p
    intro z hz
    obtain ⟨Y,hY,hQ⟩ := hD z hz
    exact hp z ⟨Y,⟨hY.symm ▸ hz,hQ⟩,hY⟩
  obtain ⟨Y,hY,j,hj,h⟩ := exists_summand P x hcl ht0 hε
  exact ⟨Y,hY.1,hY.2,j,hj,h⟩


end Hierarchy.ForceSelection

end OAI
