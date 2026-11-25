import OAI.LinearAlgebra.FiniteFourier.PhasePrice
import OAI.LinearAlgebra.FiniteFourier.MatrixWire

/-! # Prices at the two collapsed rectangle placements

Each endpoint groups the four phase registers into two pairs. The grouped
coefficient matrix differs from the displayed height- or width-zero flattening
by a bijection on each coordinate basis. A spectral price on two occupied
sites is their distance times the base-two logarithm of the matrix rank.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical NNReal

variable {K : Type*} [Field K] {R C : Type} [Fintype R] [Fintype C]

private def pairCoordinates {A : Type} (V : A → Type) (a b : A)
    (h : Function.Bijective (![a,b] : Fin 2 → A)) : (∀ i, V i) ≃ V a × V b :=
  let e := Equiv.ofBijective (![a,b] : Fin 2 → A) h
  (Equiv.piCongrLeft V e).symm.trans (piFinTwoEquiv _)

/-- At width zero the bottom and top rows are the two remaining sites. -/
def widthPartition : Fin 4 → Fin 2 := ![1,1,0,0]

/-- At height zero the left and right columns are the two remaining sites. -/
def heightPartition : Fin 4 → Fin 2 := ![0,1,0,1]

private def widthOutput (M : Matrix R C K) :
    ((phaseRaw M).group widthPartition).Leg 0 ≃ R × C :=
  pairCoordinates (fun i : {i // widthPartition i = 0} ↦ phaseLeg R C i.val)
    ⟨2, rfl⟩ ⟨3, rfl⟩ (by decide)

private def widthInput (M : Matrix R C K) :
    ((phaseRaw M).group widthPartition).Leg 1 ≃ R × C :=
  pairCoordinates (fun i : {i // widthPartition i = 1} ↦ phaseLeg R C i.val)
    ⟨0, rfl⟩ ⟨1, rfl⟩ (by decide)

private def heightLeft (M : Matrix R C K) :
    ((phaseRaw M).group heightPartition).Leg 0 ≃ R × R :=
  pairCoordinates (fun i : {i // heightPartition i = 0} ↦ phaseLeg R C i.val)
    ⟨2, rfl⟩ ⟨0, rfl⟩ (by decide)

private def heightRight (M : Matrix R C K) :
    ((phaseRaw M).group heightPartition).Leg 1 ≃ C × C :=
  pairCoordinates (fun i : {i // heightPartition i = 1} ↦ phaseLeg R C i.val)
    ⟨3, rfl⟩ ⟨1, rfl⟩ (by decide)

/-- Regrouping input and output produces the diagonal operator indexed by register pairs. -/
theorem rank_phaseRaw_width (M : Matrix R C K) :
    (twoSiteMatrix ((phaseRaw M).group widthPartition)).rank = (phaseWidthZero M).rank :=
  Matrix.rank_submatrix (phaseWidthZero M) (widthOutput M) (widthInput M)

/-- Regrouping left and right produces the original matrix on the diagonal subspaces. -/
theorem rank_phaseRaw_height (M : Matrix R C K) :
    (twoSiteMatrix ((phaseRaw M).group heightPartition)).rank = (phaseHeightZero M).rank :=
  Matrix.rank_submatrix (phaseHeightZero M) (heightLeft M) (heightRight M)

/-- At a two-site placement the price of every tensor is determined by the rank of its matrix. -/
theorem twoSite_price_eq_dist_mul_log_rank {X : Type*} [MetricSpace X] (P : SpectralPlacementPrices K X)
    (T : Raw.{0} (Fin 2) K) (p : Fin 2 → X) :
    P.price T p = dist (p 0) (p 1) * Real.logb 2 (twoSiteMatrix T).rank := by
  by_cases hz : T.coeff = 0
  · have hm : twoSiteMatrix T = 0 := by ext i j; exact congrFun hz _
    rw [P.zero_tensor _ hz, hm, Matrix.rank_zero]
    simp
  by_cases hd : p 0 = p 1
  · have he : p = fun _ ↦ p 0 := by
      funext i
      fin_cases i <;> simp [hd]
    rw [he, P.collapsed, dist_self, zero_mul]
  let e : Fin 2 ↪ X := ⟨p, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | exact (hd h).elim | exact (hd h.symm).elim⟩
  obtain ⟨φ, hφ⟩ := P.normalized e
  have hcast : φ.val ((twoSiteMatrix T).rank : TensorClass (Fin 2) K) = ((twoSiteMatrix T).rank : ℝ≥0) :=
    map_natCast (normalizedSpectrum.toRingHom φ) _
  have hh := hφ T hz
  rw [P.wire, ofRaw_eq_iff.mpr (twoSite_equivalent_wire T), ofRaw_diagonal_fin_eq_natCast,
    hcast] at hh
  exact_mod_cast hh

private def widthEndpoints (L : ℝ) : Fin 2 → Plane :=
  ![WithLp.toLp 2 ![0,-L/2], WithLp.toLp 2 ![0,L/2]]

private def heightEndpoints (W : ℝ) : Fin 2 → Plane :=
  ![WithLp.toLp 2 ![-W/2,0], WithLp.toLp 2 ![W/2,0]]

private theorem rectangle_width_zero (L : ℝ) :
    rectangleSites L 0 = widthEndpoints L ∘ widthPartition := by
  funext i
  fin_cases i <;> simp [rectangleSites, widthEndpoints, widthPartition]

private theorem rectangle_height_zero (W : ℝ) :
    rectangleSites 0 W = heightEndpoints W ∘ heightPartition := by
  funext i
  fin_cases i <;> simp [rectangleSites, heightEndpoints, heightPartition]

private theorem dist_widthEndpoints {L : ℝ} (hL : 0 ≤ L) :
    dist (widthEndpoints L 0) (widthEndpoints L 1) = L := by
  simp [widthEndpoints, PiLp.dist_eq_of_L2, Fin.sum_univ_two, Real.dist_eq,
    show -L/2-L/2 = -L by ring, Real.sqrt_sq hL]

private theorem dist_heightEndpoints {W : ℝ} (hW : 0 ≤ W) :
    dist (heightEndpoints W 0) (heightEndpoints W 1) = W := by
  simp [heightEndpoints, PiLp.dist_eq_of_L2, Fin.sum_univ_two, Real.dist_eq,
    show -W/2-W/2 = -W by ring, Real.sqrt_sq hW]

theorem fourierPhasePrice_width_zero (P : SpectralPlacementPrices K Plane)
    (M : Matrix R C K) {L : ℝ} (hL : 0 ≤ L) :
    rectanglePrice (fourierPhasePrice P) M L 0 =
      L * Real.logb 2 (∑ r, (Finset.univ.filter fun c ↦ M r c ≠ 0).card : ℕ) := by
  rw [rectanglePrice, fourierPhasePrice, rectangle_width_zero, P.group, twoSite_price_eq_dist_mul_log_rank,
    dist_widthEndpoints hL, rank_phaseRaw_width, rank_phaseWidthZero]

theorem fourierPhasePrice_height_zero (P : SpectralPlacementPrices K Plane)
    (M : Matrix R C K) {W : ℝ} (hW : 0 ≤ W) :
    rectanglePrice (fourierPhasePrice P) M 0 W = W * Real.logb 2 M.rank := by
  rw [rectanglePrice, fourierPhasePrice, rectangle_height_zero, P.group, twoSite_price_eq_dist_mul_log_rank,
    dist_heightEndpoints hW, rank_phaseRaw_height, rank_phaseHeightZero]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
