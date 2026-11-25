import OAI.LinearAlgebra.SpectralBooks.GridPrivateWidth
import OAI.LinearAlgebra.SpectralBooks.MetricLimitPrice
import OAI.LinearAlgebra.SpectralBooks.WidthLimit

/-! # Diagonal prices in the ultralimit of the doubled grids

A placement of binary diagonal indices pays at most the sum of their displacements.
This gives a price on finite sets of points of the separated ultralimit, even when
indices with different representatives coincide in the limit. For the fixed list
of marked corners its price is exactly the price of the union of the finite grids.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open Filter HyperbolicObstruction MetricLimit
open scoped Topology Classical

section

/-- Transport of the binary diagonal, whose local dimensions are two. -/
def DiagonalTransport {Y : Type*} [MetricSpace Y] (δ : Finset Y → ℝ) : Prop :=
  ∀ (k : ℕ) (p q : Fin k → Y),
    dist (δ (Finset.univ.image p)) (δ (Finset.univ.image q)) ≤ ∑ a, dist (p a) (q a)

theorem DiagonalTransport.finite {Y A : Type*} [MetricSpace Y] [Fintype A]
    {δ : Finset Y → ℝ} (h : DiagonalTransport δ) (p q : A → Y) :
    dist (δ (Finset.univ.image p)) (δ (Finset.univ.image q)) ≤ ∑ a, dist (p a) (q a) := by
  let e := (Fintype.equivFin A).symm
  have himage (f : A → Y) : Finset.univ.image (f ∘ e) = Finset.univ.image f := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, e.surjective.exists]
  simpa only [himage, Function.comp_apply, e.sum_comp (fun a ↦ dist (p a) (q a))] using
    h _ (p ∘ e) (q ∘ e)

/-- For a diagonal, the transport bound also follows directly from the wire
law and the inequality for intersecting sets. -/
theorem diagonalTransport_of_wire {Y : Type*} [MetricSpace Y] (δ : Finset Y → ℝ)
    (hw : ∀ x y, δ {x, y} = dist x y) (hs : IntersectingSubmodular δ)
    (hm : ∀ ⦃S T⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T) : DiagonalTransport δ := by
  have hz (x : Y) : δ {x} = 0 := by simpa using hw x x
  intro k p q
  by_cases hk : Nonempty (Fin k)
  · have bound (f g : Fin k → Y) : δ (Finset.univ.image f) - δ (Finset.univ.image g) ≤
        ∑ i, dist (f i) (g i) := by
      let Q := Finset.univ.image g
      have step (T : Finset (Fin k)) :
          δ (Q ∪ T.image f) ≤ δ Q + ∑ i ∈ T, dist (f i) (g i) := by
        induction T using Finset.induction_on with
        | empty => simp
        | @insert i T hi ih =>
          have hsub : {g i} ⊆ Q ∪ T.image f :=
            Finset.singleton_subset_iff.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
          have h := intersectingSubmodular_union_increment hs hm
            (Finset.singleton_nonempty (g i)) hsub {f i}
          rw [Finset.singleton_union, hw, hz, sub_zero, dist_comm (g i)] at h
          rw [Finset.image_insert, Finset.union_insert, Finset.sum_insert hi]
          rw [Finset.union_singleton] at h
          linarith
      have hh := hm (Finset.univ_nonempty.image f) (Finset.subset_union_right (s₁ := Q))
      linarith [step Finset.univ]
    rw [Real.dist_eq, abs_le]
    refine ⟨?_, bound p q⟩
    have h := bound q p
    simp_rw [dist_comm (q _) (p _)] at h
    linarith
  · have : IsEmpty (Fin k) := not_nonempty_iff.mp hk
    simp

variable {U : Ultrafilter ℕ} {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {o : ∀ n, X n}

private def diagRep (x : Space (U := U) (o := o)) : Bounded U X o :=
  (SeparationQuotient.surjective_mk x).choose

private theorem point_diagRep (x : Space (U := U) (o := o)) : point (diagRep x) = x :=
  (SeparationQuotient.surjective_mk x).choose_spec

/-- The price of the binary diagonal on a finite set in the separated ultralimit. -/
def metricLimitDiagonal (δ : ∀ n, Finset (X n) → ℝ)
    (S : Finset (Space (U := U) (o := o))) : ℝ :=
  limUnder (U : Filter ℕ) fun n ↦ δ n (S.image fun x ↦ (diagRep x).val n)

/-- A finite list of bounded representatives computes the price on its set of limit sites. -/
theorem tendsto_metricLimitDiagonal {A : Type*} [Fintype A] [Nonempty A]
    (δ : ∀ n, Finset (X n) → ℝ) (hz : ∀ n x, δ n {x} = 0)
    (hm : ∀ n, DiagonalTransport (δ n)) (p : A → Bounded U X o) :
    Tendsto (fun n ↦ δ n (Finset.univ.image fun a ↦ (p a).val n)) (U : Filter ℕ)
      (𝓝 (metricLimitDiagonal δ (Finset.univ.image (point ∘ p)))) := by
  let H := fun n (x : A → X n) ↦ δ n (Finset.univ.image x)
  have hzero (n : ℕ) (x : X n) : H n (fun _ ↦ x) = 0 := by
    dsimp [H]
    rw [Finset.image_const Finset.univ_nonempty, hz]
  have hmove (n : ℕ) (x y : A → X n) :
      dist (H n x) (H n y) ≤ ∑ a, dist (x a) (y a) * 1 := by
    simpa [H] using (hm n).finite x y
  let q := diagRep ∘ point ∘ p
  have he : point ∘ q = point ∘ p := funext fun _ ↦ point_diagRep _
  have h := tendsto_metricLimitPrice (fun _ ↦ (1 : ℝ)) H hzero hmove q
  rw [he] at h
  have hq : metricLimitDiagonal δ (Finset.univ.image (point ∘ p)) =
      metricLimitPrice H (point ∘ p) := by
    simpa only [metricLimitDiagonal, Finset.image_image, H, q, Function.comp_def] using h.limUnder_eq
  rw [hq]
  exact tendsto_metricLimitPrice _ H hzero hmove p

private theorem image_subtype_univ {A B : Type*} (S : Finset A) (f : A → B) :
    Finset.univ.image (fun x : S ↦ f x.val) = S.image f := by
  ext b
  simp

private theorem tendsto_diagRep (δ : ∀ n, Finset (X n) → ℝ) (hz : ∀ n x, δ n {x} = 0)
    (hm : ∀ n, DiagonalTransport (δ n)) (S : Finset (Space (U := U) (o := o))) (hS : S.Nonempty) :
    Tendsto (fun n ↦ δ n (S.image fun x ↦ (diagRep x).val n)) (U : Filter ℕ) (𝓝 (metricLimitDiagonal δ S)) := by
  let := hS.to_subtype
  have h := tendsto_metricLimitDiagonal δ hz hm (fun x : S ↦ diagRep x.val)
  have he (n : ℕ) := image_subtype_univ S (fun x ↦ (diagRep x).val n)
  simp only [Function.comp_def, point_diagRep, he] at h
  simpa only [Finset.univ_eq_attach, Finset.attach_image_val] using h

/-- Monotonicity of diagonal prices on nonempty finite sets passes to the ultralimit. -/
theorem metricLimitDiagonal_mono (δ : ∀ n, Finset (X n) → ℝ) (hz : ∀ n x, δ n {x} = 0)
    (ht : ∀ n, DiagonalTransport (δ n))
    (hm : ∀ n ⦃S T⦄, S.Nonempty → S ⊆ T → δ n S ≤ δ n T)
    {S T : Finset (Space (U := U) (o := o))} (hS : S.Nonempty) (hST : S ⊆ T) :
    metricLimitDiagonal δ S ≤ metricLimitDiagonal δ T := by
  apply le_of_tendsto_of_tendsto' (tendsto_diagRep δ hz ht S hS) (tendsto_diagRep δ hz ht T (hS.mono hST))
  exact fun n ↦ hm n (hS.image _) (Finset.image_subset_image hST)

/-- Intersecting submodularity also passes to the separated ultralimit. -/
theorem metricLimitDiagonal_submodular (δ : ∀ n, Finset (X n) → ℝ) (hz : ∀ n x, δ n {x} = 0)
    (ht : ∀ n, DiagonalTransport (δ n))
    (hm : ∀ n ⦃S T⦄, S.Nonempty → S ⊆ T → δ n S ≤ δ n T)
    (hs : ∀ n, IntersectingSubmodular (δ n)) :
    IntersectingSubmodular (metricLimitDiagonal (U := U) (o := o) δ) := by
  intro A B hI
  have hA := hI.mono Finset.inter_subset_left
  have hB := hI.mono Finset.inter_subset_right
  have hU := hA.mono (Finset.subset_union_left (s₂ := B))
  apply le_of_tendsto_of_tendsto' ((tendsto_diagRep δ hz ht _ hU).add (tendsto_diagRep δ hz ht _ hI))
    ((tendsto_diagRep δ hz ht _ hA).add (tendsto_diagRep δ hz ht _ hB))
  intro n
  let f := fun x : Space (U := U) (o := o) ↦ (diagRep x).val n
  have hsub : (A ∩ B).image f ⊆ A.image f ∩ B.image f :=
    Finset.subset_inter (Finset.image_subset_image Finset.inter_subset_left)
      (Finset.image_subset_image Finset.inter_subset_right)
  have hi := hm n (hI.image f) hsub
  have hh := hs n ((hI.image f).mono hsub)
  change δ n ((A ∪ B).image f) + δ n ((A ∩ B).image f) ≤ δ n (A.image f) + δ n (B.image f)
  rw [Finset.image_union]
  linarith

namespace DoubledGridFamily

variable {ι : Type*} [Fintype ι] (G : DoubledGridFamily ι o)

/-- Private equality for a finite diagonal expressed in the doubled coordinates. -/
def HasPrivateDiagonalPrices (δ : ∀ n, Finset (X n) → ℝ) : Prop :=
  ∀ n k (T : Finset (cubeGrid ι n)) (hT : T.Nonempty),
    δ n (T.image (G.site n k)) = meanWidth (T.image Subtype.val) (hT.image _)

/-- A private page in the ultralimit has its Euclidean diagonal price on every
nonempty finite configuration of the doubled cube. -/
theorem chart_diagonal_price (hU : (U : Filter ℕ) ≤ atTop)
    (δ : ∀ n, Finset (X n) → ℝ) (hz : ∀ n x, δ n {x} = 0)
    (ht : ∀ n, DiagonalTransport (δ n)) (hpriv : G.HasPrivateDiagonalPrices δ)
    (k : Bool) (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty)
    (hc : (S : Set _) ⊆ coordinateCube ι 2) :
    metricLimitDiagonal δ (S.image (G.chart U k)) = meanWidth S hS := by
  let := hS.to_subtype
  let a (n : ℕ) (x : S) : cubeGrid ι n := ⟨_, gridPoint_mem n x.val⟩
  let p (x : S) := G.gridSection U k x.val
  have hl := tendsto_metricLimitDiagonal δ hz ht p
  have hw := tendsto_meanWidth_image (fun x : S ↦ tendsto_gridPoint (hc x.property))
  have he (n : ℕ) : δ n (Finset.univ.image (fun x : S ↦ (p x).val n)) =
      meanWidth (Finset.univ.image (fun x : S ↦ gridPoint n x.val)) (Finset.univ_nonempty.image _) := by
    simpa only [Finset.image_image, Function.comp_def, p, gridSection, a] using
      hpriv n k (Finset.univ.image (a n)) (Finset.univ_nonempty.image _)
  have hh := tendsto_nhds_unique hl ((hw.mono_left hU).congr fun n ↦ (he n).symm)
  change metricLimitDiagonal δ (Finset.univ.image (fun x : S ↦ G.chart U k x.val)) = _ at hh
  rw [image_subtype_univ S (G.chart U k)] at hh
  simp only [Finset.univ_eq_attach, Finset.attach_image_val] at hh
  exact hh

private theorem corners_mem_grid (n : ℕ) {z : EuclideanSpace ℝ ι}
    (hz : z ∈ coordinateCubeCorners ι 2) : z ∈ cubeGrid ι n := by
  rw [doubled_cube_corners] at hz
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
  exact double_corner_mem_cubeGrid n hv

private theorem width_cubeGrid_eq_corners (n : ℕ) :
    meanWidth (cubeGrid ι n) ⟨_, zero_mem_cubeGrid ι n⟩ =
      meanWidth (coordinateCubeCorners ι 2) (coordinateCubeCorners_nonempty ι 2) := by
  have hsub : coordinateCubeCorners ι 2 ⊆ cubeGrid ι n := fun _ hz ↦ corners_mem_grid n hz
  have h := meanWidth_union_of_subset_convexHull (coordinateCubeCorners_nonempty ι 2)
    (T := cubeGrid ι n) (by rw [convexHull_coordinateCubeCorners (by norm_num : (0 : ℝ) ≤ 2)]
                            exact cubeGrid_subset ι n)
  convert! h using 1
  congr 1
  convert! (Finset.union_eq_right.mpr hsub).symm using 1
  congr! 3

private theorem image_bool_prod {A Y : Type*} [Fintype A] (f : Bool → A → Y) :
    Finset.univ.image (fun j : Bool × A ↦ f j.1 j.2) =
      Finset.univ.image (f false) ∪ Finset.univ.image (f true) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Prod.exists, Bool.exists_bool]

/-- The diagonal on the union of the outer corner sets in the two limiting
pages costs three times the width of the inner cube. The finite grid unions
are allowed to have unbounded cardinality. -/
theorem corner_union_limit_price
    (δ : ∀ n, Finset (X n) → ℝ) (hz : ∀ n x, δ n {x} = 0)
    (ht : ∀ n, DiagonalTransport (δ n))
    (hm : ∀ n ⦃S T⦄, S.Nonempty → S ⊆ T → δ n S ≤ δ n T)
    (hs : ∀ n, IntersectingSubmodular (δ n))
    (hpriv : G.HasPrivateDiagonalPrices δ)
    (hfull : ∀ n, δ n (G.gridSites n false ∪ G.gridSites n true) = 3 * innerCubeWidth ι) :
    metricLimitDiagonal δ ((coordinateCubeCorners ι 2).image (G.chart U false) ∪
      (coordinateCubeCorners ι 2).image (G.chart U true)) = 3 * innerCubeWidth ι := by
  let W := coordinateCubeCorners ι 2
  have hW : W.Nonempty := coordinateCubeCorners_nonempty ι 2
  let := hW.to_subtype
  let a (n : ℕ) (z : W) : cubeGrid ι n := ⟨z.val, corners_mem_grid n z.property⟩
  let p (j : Bool × W) := G.gridSection U j.1 j.2.val
  have hfix (n : ℕ) (k : Bool) (z : W) :
      (p (k,z)).val n = G.site n k (a n z) :=
    congrArg (G.site n k) (Subtype.ext (gridPoint_eq_of_mem (corners_mem_grid n z.property)))
  have hlim := tendsto_metricLimitDiagonal δ hz ht p
  have him : Finset.univ.image (point ∘ p) =
      W.image (G.chart U false) ∪ W.image (G.chart U true) := by
    change Finset.univ.image (fun j : Bool × W ↦ G.chart U j.1 j.2.val) = _
    rw [image_bool_prod (fun k (z : W) ↦ G.chart U k z.val),
      image_subtype_univ W (G.chart U false), image_subtype_univ W (G.chart U true)]
  rw [him] at hlim
  apply tendsto_nhds_unique hlim
  apply tendsto_const_nhds.congr
  intro n
  let T := Finset.univ.image (a n)
  have hT : T.Nonempty := Finset.univ_nonempty.image _
  have ha : T.image Subtype.val = W := by
    simp only [T, Finset.image_image, Function.comp_def, a, Finset.univ_eq_attach, Finset.attach_image_val]
  let : Nonempty (cubeGrid ι n) := ⟨⟨0, zero_mem_cubeGrid ι n⟩⟩
  have he (k : Bool) : δ n (T.image (G.site n k)) = δ n (G.gridSites n k) := by
    rw [hpriv n k T hT, gridSites, hpriv n k _ Finset.univ_nonempty]
    simpa only [ha, Finset.univ_eq_attach, Finset.attach_image_val, W] using
      (width_cubeGrid_eq_corners (ι := ι) n).symm
  have hi (k : Bool) : T.image (G.site n k) ⊆ G.gridSites n k :=
    Finset.image_subset_image (Finset.subset_univ _)
  have hfinite := union_price_eq_of_eq_on_subsets (hs n) (hm n) (hT.image _) (hT.image _)
    (hi false) (hi true) (he false) (he true)
  have hj : Finset.univ.image (fun j : Bool × W ↦ (p j).val n) =
      T.image (G.site n false) ∪ T.image (G.site n true) := by
    rw [image_bool_prod (fun k (z : W) ↦ (p (k,z)).val n)]
    simp only [hfix, T, Finset.image_image, Function.comp_def]
  rw [hj, hfinite, hfull]

end DoubledGridFamily

namespace DoubledGridPrices

variable {ι : Type*} [Fintype ι] (P : DoubledGridPrices ι X)

/-- The price retained on finite sets of points in the pointed ultralimit of
the doubled configurations. -/
abbrev limitDiagonal (U : Ultrafilter ℕ) :=
  metricLimitDiagonal (U := U) (o := fun n ↦ P.place n gridCenter) P.diagonal

theorem diagonal_singleton (n : ℕ) (x : X n) : P.diagonal n {x} = 0 := by
  simpa using P.wire n x x

theorem diagonal_transport (n : ℕ) : DiagonalTransport (P.diagonal n) :=
  diagonalTransport_of_wire _ (P.wire n) (P.submod n) (P.mono n)

theorem chart_width (hU : (U : Filter ℕ) ≤ atTop) (k : Bool)
    (S : Finset (EuclideanSpace ℝ ι)) (hS : S.Nonempty) (hc : (S : Set _) ⊆ coordinateCube ι 2) :
    P.limitDiagonal U (S.image (P.family.chart U k)) = meanWidth S hS :=
  P.family.chart_diagonal_price hU _ P.diagonal_singleton P.diagonal_transport
    P.private_grid_price k S hS hc

theorem chart_corner_union_price (U : Ultrafilter ℕ) :
    P.limitDiagonal U ((coordinateCubeCorners ι 2).image (P.family.chart U false) ∪
      (coordinateCubeCorners ι 2).image (P.family.chart U true)) = 3 * innerCubeWidth ι :=
  P.family.corner_union_limit_price _ P.diagonal_singleton P.diagonal_transport
    P.mono P.submod P.private_grid_price P.grid_union_price

/-- Equation (book-independence) for the actual limit price from the finite
doubled grids in CAT(0) spaces. -/
theorem chart_independence (hU : (U : Filter ℕ) ≤ atTop) (hX : ∀ n, CATZero (X n))
    (L N : Finset (EuclideanSpace ℝ ι)) (hL : (L : Set _) ⊆ coordinateCube ι 2)
    (hN : (N : Set _) ⊆ coordinateCube ι 2) :
    let f := P.family.chart U false
    let g := P.family.chart U true
    let K := (coordinateCubeCorners ι 1).image f
    P.limitDiagonal U (K ∪ L.image f ∪ N.image g) =
      P.limitDiagonal U (K ∪ L.image f) + P.limitDiagonal U (K ∪ N.image g) - P.limitDiagonal U K :=
  doubled_cube_diagonal_independence
    (metricLimitDiagonal_submodular _ P.diagonal_singleton P.diagonal_transport P.mono P.submod)
    (fun _ _ hS hST ↦ metricLimitDiagonal_mono _ P.diagonal_singleton P.diagonal_transport P.mono hS hST)
    _ _ (P.family.charts_agree U hU hX) (P.chart_width hU false) (P.chart_width hU true)
    (P.chart_corner_union_price U) L N hL hN

end DoubledGridPrices
end

end

end SpectralBooks
end LinearAlgebra
end OAI
