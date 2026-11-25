import OAI.LinearAlgebra.SpectralBooks.Book.BookTangentLimit
import OAI.LinearAlgebra.SpectralBooks.Book.BookPriceFlat
import OAI.LinearAlgebra.SpectralBooks.GridPriceLimit
import OAI.LinearAlgebra.SpectralBooks.SpectralFlatLaw

/-!
# The contracted configurations in the tangent hull

The original points at fraction `hM` toward the corners and toward `x` have
bounded representatives in the rescaled ultralimit. The flat law on the
Euclidean hull computes the two limits of their diagonal prices, before and
after adjoining the point displaced by `he`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
namespace Book

open HyperbolicObstruction Filter Set
open scoped Topology RealInnerProductSpace Classical

private theorem image_univ_subtype {U V : Type*} (T : Finset U) (f : U → V) :
    (Finset.univ.image fun p : T ↦ f p.val) = T.image f := by
  ext v
  simp

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace (Lift E)]

/-- The contraction of the occupied center, all corners, and the opposite
point realizes the width increment in `eq:book-marginal`. The flat-law
hypothesis applies to finite configurations in isometrically embedded
Euclidean apex hulls of the limiting price. -/
theorem tendsto_contractedSites_widthIncrement (hX : CATZero X) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ atTop) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (h₀ : Tendsto s atTop (𝓝 0))
    {U : Set E} {φ : E → X} (hφ : ∀ u ∈ U, ∀ z ∈ U, dist (φ u) (φ z) = dist u z)
    {y g : E} (hy : U ∈ 𝓝 y) (x : X) (hg : HasGradientAt (fun u ↦ dist (φ u) x) g y)
    (C : Finset E) (hC : (C : Set E) ⊆ U) (e : E) {M : ℝ} (hM : 0 ≤ M)
    (δ : Finset X → ℝ) (hz : ∀ p, δ {p} = 0) (hmove : DiagonalTransport δ)
    (hflat : ∀ (a : E) (H : ℝ) (F : flatApexHull a H → Blowup ω hs (φ y)), Isometry F →
      ∀ (V : Finset (flatApexHull a H)) (hV : V.Nonempty),
      blowupDiagonal ω hs (φ y) δ (V.image F) = meanWidth (V.image Subtype.val) (hV.image _)) :
    let S := insert (liftedDirection g (dist (φ y) x)) (centeredCorners C y)
    Tendsto (fun n ↦
      let A := contractedSites (CATZero.segment hX) (φ y) (oldConfiguration φ x C y) (s n * M)
      (δ (insert (φ (y + s n • e)) A) - δ A) / s n) (ω : Filter ℕ)
      (𝓝 (widthIncrement S (Finset.insert_nonempty _ _) (horizontal e) M)) := by
  let Xy := liftedDirection g (dist (φ y) x)
  let A := M • Xy
  let B := flatApexHull A.fst A.snd
  let apex : B := ⟨A, flatApexHull_apex_mem _ _⟩
  let base (v : E) : B := ⟨horizontal v, flatApexHull_base_mem _ _ _⟩
  let ray := raySection (φ := φ) (y := y) ω hs hX x hM
  let page := pageSection ω hs hφ hy
  obtain ⟨F, hF, hbase, hapex⟩ := exists_tangentHull_isometry ω hs hφ hy hX x hM hω h₀ hg
  let Pair := BlowupSection ω hs (φ y) × B
  let horizontalPair (v : E) : Pair := (page v, base v)
  let rayPair : Pair := (ray, apex)
  let R : Finset Pair := insert rayPair (insert (horizontalPair 0)
    (C.image (fun z ↦ horizontalPair (M • (z - y)))))
  let S := insert Xy (centeredCorners C y)
  let raw (n : ℕ) (p : Pair) := (p.1.val n).val
  let coords (p : Pair) : Lift E := p.2.val
  have paired (p : Pair) (hp : p ∈ insert (horizontalPair e) R) : MetricLimit.point p.1 = F p.2 := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact (hbase e).symm
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hapex.symm
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact (hbase 0).symm
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hp
    exact (hbase _).symm
  have limit (T : Finset Pair) (hT : T.Nonempty) (hsub : T ⊆ insert (horizontalPair e) R) :
      Tendsto (fun n ↦ δ (T.image (raw n)) / s n) (ω : Filter ℕ)
        (𝓝 (meanWidth (T.image coords) (hT.image _))) := by
    let := hT.to_subtype
    let z (p : T) := p.val.1
    have hc := tendsto_blowupDiagonal ω hs (φ y) δ hz hmove.finite z
    have hl : (Finset.univ.image fun p : T ↦ MetricLimit.point (z p)) = (T.image Prod.snd).image F := by
      rw [Finset.image_image, ← image_univ_subtype T (F ∘ Prod.snd)]
      exact Finset.image_congr fun p _ ↦ paired p.val (hsub p.prop)
    rw [hl, hflat _ _ F hF _ (hT.image Prod.snd)] at hc
    have heval (n : ℕ) :
        Finset.univ.image (fun i ↦ ((z i).val n).val) = T.image (raw n) :=
      image_univ_subtype T (raw n)
    simpa only [heval, Finset.image_image, Function.comp_def, coords] using hc
  have hnR : R.Nonempty := Finset.insert_nonempty _ _
  let Cₙ (n : ℕ) := contractedSites (CATZero.segment hX) (φ y) (oldConfiguration φ x C y) (s n * M)
  have rawEq : ∀ᶠ n in atTop, R.image (raw n) = Cₙ n := by
    have hscale : Tendsto (fun n ↦ s n * M) atTop (𝓝 0) := by simpa using h₀.mul_const M
    filter_upwards [eventually_raySection (φ := φ) (y := y) ω hs hX x hM h₀,
      eventually_pageSection ω hs hφ hy h₀ (0 : E),
      (C.eventually_all).mpr (fun z hz ↦ eventually_pageSection_segment ω hs hφ hy hX
        hM h₀ (hC hz)), hscale.eventually_lt_const zero_lt_one] with n hr hc hz hn
    have hself : CATZero.segment hX (φ y) (φ y) (s n * M) = φ y :=
      dist_eq_zero.mp (by rw [dist_comm, CATZero.segment_left hX _ _
        ⟨mul_nonneg (hs n).le hM, hn.le⟩, dist_self, mul_zero])
    simp only [raw, R, Cₙ, contractedSites, oldConfiguration, Finset.image_insert,
      Finset.image_image, Function.comp_def, rayPair, horizontalPair, ray, page, hr, hc,
      smul_zero, add_zero, hself]
    rw [Finset.image_congr hz]
    simp [Finset.insert_comm]
  have Rcoords : R.image coords = S.image (M • ·) := by
    simp only [coords, R, S, Finset.image_insert, Finset.image_image, Function.comp_def,
      centeredCorners, horizontalPair, rayPair, base, apex, A, smul_zero]
    have hzero : horizontal (0 : E) = 0 := rfl
    have hsm (z : E) : horizontal (M • z) = M • horizontal z := by
      apply (WithLp.equiv 2 _).injective
      exact Prod.ext rfl (by simp [horizontal])
    simp only [hzero, hsm]
  have rc := limit R hnR (Finset.subset_insert (horizontalPair e) R)
  have re := limit (insert (horizontalPair e) R) (Finset.insert_nonempty _ _) (Finset.Subset.refl _)
  have he : (insert (horizontalPair e) R).image coords = insert (horizontal e) (S.image (M • ·)) := by
    rw [Finset.image_insert, Rcoords]
  simp only [he, Rcoords] at rc re
  have hwidth : meanWidth (insert (horizontal e) (S.image (M • ·))) (Finset.insert_nonempty _ _) -
      meanWidth (S.image (M • ·)) ((Finset.insert_nonempty _ _).image _) =
      widthIncrement S (Finset.insert_nonempty _ _) (horizontal e) M := by
    unfold widthIncrement
    congr!
  have hw := re.sub rc
  rw [hwidth] at hw
  apply hw.congr'
  filter_upwards [hω rawEq, hω (eventually_pageSection ω hs hφ hy h₀ e)] with n hr hpe
  simp only [Finset.image_insert, hr, raw, horizontalPair, page, hpe, Cₙ, sub_div]

/-- The contracted limit for the actual spectral-space diagonal follows from
the flat law on convex Euclidean hulls over the same field. -/
theorem spectral_contractedSites_widthIncrement {K : Type*} [Field K] (P : SpectralPlacementPrices K X)
    (hX : CATZero X) (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (h₀ : Tendsto s atTop (𝓝 0))
    {U : Set E} {φ : E → X} (hφ : ∀ u ∈ U, ∀ z ∈ U, dist (φ u) (φ z) = dist u z)
    {y g : E} (hy : U ∈ 𝓝 y) (x : X) (hg : HasGradientAt (fun u ↦ dist (φ u) x) g y)
    (C : Finset E) (hC : (C : Set E) ⊆ U) (e : E) {M : ℝ} (hM : 0 ≤ M)
    (hflat : ∀ (a : E) (H : ℝ) (Q : SpectralPlacementPrices K (flatApexHull a H))
      (T : Finset (flatApexHull a H)) (hT : T.Nonempty),
      Q.diagonal T = meanWidth (T.image Subtype.val) (hT.image _)) :
    let S := insert (liftedDirection g (dist (φ y) x)) (centeredCorners C y)
    Tendsto (fun n ↦
      let A := contractedSites (CATZero.segment hX) (φ y) (oldConfiguration φ x C y) (s n * M)
      (P.diagonal (insert (φ (y + s n • e)) A) - P.diagonal A) / s n) (ω : Filter ℕ)
      (𝓝 (widthIncrement S (Finset.insert_nonempty _ _) (horizontal e) M)) := by
  apply tendsto_contractedSites_widthIncrement hX ω hω hs h₀ hφ hy x hg C hC e hM
    P.diagonal P.diagonal_singleton (fun _ ↦ P.diagonal_transport)
  intro a H F hF V hV
  rw [blowupDiagonal_spectralPrices _ _ _ _ _ (hV.image F),
    ← SpectralPlacementPrices.diagonal_pullback _ F hF]
  exact hflat a H _ V hV

/-- On an isometrically embedded Euclidean hull, the field's spectral diagonal
has its normalized width over every field. Geodesic convexity is inherited
from the original price before rescaling. -/
theorem blowupDiagonal_flatApexHull {X E K : Type} [Field K] [MetricSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace (Lift E)] [BorelSpace (Lift E)]
    (P : SpectralPlacementPrices K X) (hX : CATZero X) (hjoint : P.JointlyConvexDiagonal hX)
    (ω : Ultrafilter ℕ) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (o : X)
    (a : E) (H : ℝ) (F : flatApexHull a H → Blowup ω hs o) (hF : Isometry F)
    (V : Finset (flatApexHull a H)) (hV : V.Nonempty) :
    blowupDiagonal ω hs o P.diagonal (V.image F) = meanWidth (V.image Subtype.val) (hV.image _) := by
  let Q := blowupSpectralPrices ω hs o P
  let hB := blowup_catZero hX ω hs o
  have hQ : Q.JointlyConvexDiagonal hB := fun x y t ht ↦
    blowupSpectralPrices_jointConvex ω hs o P hX _ hjoint x y ht
  let C := flatApexHull a H
  let f (v : Lift E) := if h : v ∈ C then F ⟨v, h⟩ else F ⟨_, flatApexHull_apex_mem a H⟩
  have hf (v : C) : f v.val = F v := dite_eq_left v.prop
  have hd (v : Lift E) (hv : v ∈ C) (w : Lift E) (hw : w ∈ C) :
      dist (f v) (f w) = dist v w := by
    rw [hf ⟨v,hv⟩, hf ⟨w,hw⟩, hF.dist_eq]; rfl
  have hVC : (↑(V.image Subtype.val) : Set (Lift E)) ⊆ C := by
    rintro _ hp
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hp
    exact v.prop
  rw [blowupDiagonal_spectralPrices _ _ _ _ _ (hV.image F)]
  have h := Q.flatDiagonalLaw_chart hB hQ (convex_convexHull _ _) hd
    (V.image Subtype.val) (hV.image _) hVC
  simpa only [Finset.image_image, Function.comp_def, hf] using h

end Book

end

end SpectralBooks
end LinearAlgebra
end OAI
