import OAI.Hierarchy.FlatPrices
import OAI.LinearAlgebra.SpectralBooks.WireMetricBaseChange
import OAI.LinearAlgebra.SpectralBooks.NormPatch

namespace OAI
/-! # Finite wire configurations and scalar extension for spectral flats -/

namespace Hierarchy

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor

namespace WireChart

variable {K : Type*} [Field K] {Y : Type*} [MetricSpace Y]
variable {J : Type} [Fintype J] [Nontrivial J]

theorem wire_ne_zero (K : Type*) [Field K] :
    (Raw.diagonal (Fin 2) K (Fin 2)).coeff ≠ 0 := by
  intro h
  have h0 := congrFun h (fun _ => (0 : Fin 2))
  change (Raw.diagonal (Fin 2) K (Fin 2)).coeff (fun _ => (0 : Fin 2)) = (0 : K) at h0
  simp [Raw.diagonal_coeff_at (0 : Fin 2)] at h0

/-- One scale and one spectral point realize all the distances of an injective placement. -/
theorem of_prices (P : SpectralPlacementPrices K Y) (e : J ↪ Y) :
    ∃ φ : normalizedSpectrum (S := TensorClass.{0} J K) (· ≤ ·),
      ∀ i j, rawWireDistance φ (P.price (Raw.diagonal J K (Fin 2)) e) i j = dist (e i) (e j) := by
  obtain ⟨φ, _, h⟩ := P.normalized_group e
  refine ⟨φ, fun i j => ?_⟩
  simpa [rawWireDistance, rawLogPrice] using
    (h ![i,j] _ (wire_ne_zero K)).symm.trans (P.wire (e ∘ ![i,j]))

private def pointPrices (L : Type*) [Field L] : SpectralPlacementPrices L PUnit.{1} where
  price _ _ := 0
  zero_tensor _ _ _ := rfl
  collapsed _ _ := rfl
  group _ _ _ := rfl
  wire _ := rfl
  transport T _ _ := by
    change dist (0 : ℝ) 0 ≤ ∑ i, (0 : ℝ) * Real.logb 2 (Fintype.card (T.Leg i))
    simp
  dist_le_diagonal _ _ _ := le_rfl
  normalized := by
    intro I _ _ e
    obtain ⟨i,j,hij⟩ := exists_pair_ne I
    exact False.elim (hij (e.injective (Subsingleton.elim _ _)))

/-- Joint wire data on each finite list give prices for the full metric space. -/
theorem prices_of_charts (L : Type*) [Field L] [Nonempty Y]
    (h : ∀ {J : Type} [Fintype J] [Nontrivial J] (e : J ↪ Y),
      ∃ (φ : normalizedSpectrum (S := TensorClass.{0} J L) (· ≤ ·)) (c : ℝ),
        0 < c ∧ ∀ i j, rawWireDistance φ c i j = dist (e i) (e j)) :
    Nonempty (SpectralPlacementPrices L Y) := by
  classical
  apply HasFiniteSpectralRealizationsOn.prices.{0}
  intro S hs _
  obtain ⟨o, ho⟩ := hs
  let e : (↑S : Set Y) ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  let j (x : Y) : (↑S : Set Y) := if hx : x ∈ S then ⟨x, hx⟩ else ⟨o, ho⟩
  rcases subsingleton_or_nontrivial (Fin S.card) with hsub | hnon
  · refine ⟨PUnit, inferInstance, pointPrices L, 1, zero_lt_one, fun _ => PUnit.unit, ?_⟩
    intro x hx y hy
    have hxy := congrArg Subtype.val (e.injective (Subsingleton.elim (e ⟨x,hx⟩) (e ⟨y,hy⟩)))
    change x = y at hxy
    simp [hxy]
  · let emb := e.symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ S))
    obtain ⟨φ,c,hc,hd⟩ := h emb
    obtain ⟨X,m,P,f,_,hf,_⟩ := exists_metric_price_realization φ c hc.le
    refine ⟨X,m,P,1,zero_lt_one,fun x => f (e (j x)), ?_⟩
    intro x hx y hy
    simp [hf, hd, emb, j, hx, hy]

end WireChart

/-- Scalar extension preserves all wire distances of the full spectral space. -/
theorem spectralPrices_baseChange {K L : Type*} [Field K] [Field L] [Algebra K L]
    {Y : Type*} [MetricSpace Y] [Nonempty Y] (P : SpectralPlacementPrices K Y) :
    Nonempty (SpectralPlacementPrices L Y) := by
  apply WireChart.prices_of_charts
  intro J _ _ e
  obtain ⟨φ,hφ⟩ := WireChart.of_prices P e
  obtain ⟨ψ,hψ⟩ := exists_spectrum_mapScalars (K := L) φ
  have heq : pullbackSpectrum (algebraMap K L) ψ = φ := Subtype.ext (funext hψ)
  refine ⟨ψ,_,P.diagonal_pos e,fun i j => ?_⟩
  simpa only [← heq, rawWireDistance_pullbackSpectrum] using hφ i j

theorem HasSpectralFlat.baseChange {K L : Type*} [Field K] [Field L] [Algebra K L]
    {d : ℕ} (h : HasSpectralFlat K d) : HasSpectralFlat L d :=
  h.elim fun P => spectralPrices_baseChange P

theorem HasSpectralFlat.of_prime_characteristic {p d : ℕ} [Fact p.Prime]
    (F : Type*) [Field F] [CharP F p] (h : HasSpectralFlat (ZMod p) d) :
    HasSpectralFlat F d := by
  let : Algebra (ZMod p) F := ZMod.algebra _ _
  exact h.baseChange


end Hierarchy

end OAI
