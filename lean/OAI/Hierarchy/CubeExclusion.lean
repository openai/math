import OAI.Hierarchy.FlatPrices
import OAI.LinearAlgebra.SpectralBooks.ConeFrame
import OAI.ThreeFlat.Scale
import OAI.LinearAlgebra.SpectralBooks.SpectralMetricLimit

namespace OAI
/-! # Uniform exclusion of cubes in every missing flat dimension -/

open Filter HyperbolicObstruction HyperbolicObstruction.MetricLimit
open scoped Topology BigOperators InnerProductSpace
namespace Hierarchy.CubeExclusion

open MatrixMultiplication LinearAlgebra.SpectralBooks

abbrev Vertex (d : ℕ) := Fin d → Bool

variable {d : ℕ}

def flip (v : Vertex d) : Vertex d := fun i => !(v i)

def corner (v : Vertex d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => if v i then 1 else -1)

@[simp] theorem corner_flip (v : Vertex d) : corner (flip v) = -corner v := by
  ext i
  change (if !(v i) then (1 : ℝ) else -1) = -(if v i then 1 else -1)
  cases v i <;> norm_num

theorem norm_sq (v : Vertex d) : ‖corner v‖ ^ 2 = d := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have h (i : Fin d) : (corner v i)^2 = 1 := by
    change (if v i then (1 : ℝ) else -1)^2 = 1
    cases v i <;> norm_num
  simp [h]

/-- The all-negative corner and the corners with one positive coordinate
affinely span the cube in all dimensions, including dimension two. -/
def frame : Fin (d+1) → Vertex d := Fin.cases (fun _ => false) (fun i j => decide (j=i))

noncomputable def coeff (x : EuclideanSpace ℝ (Fin d)) : Fin (d+1) → ℝ :=
  Fin.cases (-(∑ i, x i / 2)) (fun i => x i / 2)

theorem frame_expand (u : EuclideanSpace ℝ (Fin d)) :
    ∑ i, coeff u i • corner (frame i) = u := by
  classical
  ext j
  change EuclideanSpace.projₗ j (∑ i, coeff u i • corner (frame i)) = u j
  rw [map_sum, Fin.sum_univ_succ]
  simp only [map_smul, coeff, frame, Fin.cases_zero, Fin.cases_succ, smul_eq_mul]
  change - (∑ i, u i / 2) * (-1) +
    (∑ i : Fin d, u i / 2 * (if decide (j = i) then 1 else -1)) = u j
  have h (i : Fin d) : u i / 2 * (if decide (j=i) then 1 else -1) =
      - (u i / 2) + (if i=j then u j else 0) := by
    by_cases he : i=j
    · subst i; simp; ring
    · simp [he,Ne.symm he]
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp

theorem frame_inner (u v : EuclideanSpace ℝ (Fin d)) :
    ⟪u, v⟫_ℝ = ∑ i, ∑ j, coeff u i * coeff v j *
      ⟪corner (frame i), corner (frame j)⟫_ℝ := by
  calc
    ⟪u, v⟫_ℝ = ⟪∑ i, coeff u i • corner (frame i),
        ∑ j, coeff v j • corner (frame j)⟫_ℝ := by rw [frame_expand, frame_expand]
    _ = _ := by
      rw [sum_inner]
      simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem tangent_frame {X : Type*} [MetricSpace X] (h : CATZero X)
    (x : Vertex d → X)
    (hdist : ∀ i j, dist (x i) (x j) = dist (corner i) (corner j)) :
    ∃ o : X, (∀ v, o = CATZero.mid h (x v) (x (flip v))) ∧
      (∀ v, (TangentCone.coneData h o).normSq (TangentCone.log h o (x v)) = (d : ℝ)) ∧
      (∀ v, (TangentCone.coneData h o).Opposite
        (TangentCone.log h o (x v)) (TangentCone.log h o (x (flip v)))) ∧
      ∀ v w, (TangentCone.coneData h o).pairing
        (TangentCone.log h o (x v)) (TangentCone.log h o (x w)) =
          ⟪corner v, corner w⟫_ℝ := by
  have hpolar (v w : Vertex d) :
      dist (x v) (x w) ^ 2 = 2*(d : ℝ) - 2 * ⟪corner v, corner w⟫_ℝ := by
    rw [hdist, dist_eq_norm, norm_sub_sq_real, norm_sq, norm_sq]
    ring
  have hdiam (v : Vertex d) : dist (x v) (x (flip v)) ^ 2 = 4*(d : ℝ) := by
    rw [hpolar, corner_flip, inner_neg_right, real_inner_self_eq_norm_sq, norm_sq]
    ring
  let k : Vertex d := fun _ ↦ false
  let o := CATZero.mid h (x k) (x (flip k))
  have hm (v : Vertex d) : o = CATZero.mid h (x v) (x (flip v)) := by
    have hs : dist (x k) (x v) ^ 2 + dist (x v) (x (flip k)) ^ 2 +
        dist (x (flip k)) (x (flip v)) ^ 2 + dist (x (flip v)) (x k) ^ 2 = 8*(d : ℝ) := by
      rw [hpolar, hpolar, hpolar, hpolar]
      simp only [corner_flip, inner_neg_right, inner_neg_left, neg_neg]
      rw [real_inner_comm (corner v) (corner k)]
      ring
    have hq := CATZero.quadrilateral h (x k) (x v) (x (flip k)) (x (flip v))
    rw [hdiam, hdiam, hs] at hq
    apply dist_eq_zero.mp
    change dist (CATZero.mid h (x k) (x (flip k))) (CATZero.mid h (x v) (x (flip v))) = 0
    nlinarith only [hq, dist_nonneg (x := CATZero.mid h (x k) (x (flip k)))
      (y := CATZero.mid h (x v) (x (flip v)))]
  have hr (v : Vertex d) : dist o (x v) ^ 2 = (d : ℝ) := by
    rw [hm v, dist_comm, CATZero.dist_left_mid]
    nlinarith only [hdiam v]
  have hop (v : Vertex d) : (TangentCone.coneData h o).Opposite
      (TangentCone.log h o (x v)) (TangentCone.log h o (x (flip v))) := by
    rw [hm v]
    exact TangentCone.opposite_mid_logs h _ _
  refine ⟨o, hm, fun v ↦ by rw [TangentCone.normSq_log, hr], hop, ?_⟩
  have hlo (v w : Vertex d) : ⟪corner v, corner w⟫_ℝ ≤
      (TangentCone.coneData h o).pairing (TangentCone.log h o (x v))
        (TangentCone.log h o (x w)) := by
    have hl := TangentCone.pairing_log_ge h o (x v) (x w)
    rw [hr, hr, hpolar] at hl
    linarith only [hl]
  intro v w
  have hu := (TangentCone.coneData h o).opposite_pairing (TangentCone.catZero h o)
    (hop v) (TangentCone.log h o (x w))
  have hl := hlo (flip v) w
  rw [corner_flip, inner_neg_left] at hl
  exact le_antisymm (by linarith only [hu, hl]) (hlo v w)

theorem isometry_of_frame {X : Type*} [MetricSpace X] (T : ConeData X) (h : CATZero X)
    (c : Vertex d → X) (hop : ∀ v, T.Opposite (c v) (c (flip v)))
    (hgram : ∀ v w, T.pairing (c v) (c w) = ⟪corner v, corner w⟫_ℝ) :
    ∃ g : EuclideanSpace ℝ (Fin d) → X, Isometry g := by
  have hp (i : Fin (d+1)) (v : Vertex d) : T.Parallel (c (frame i))
      (c (flip (frame i))) (c v) := by
    simp [ConeData.Parallel, hgram]
  obtain ⟨f, hf⟩ := exists_gram_realization T h (fun i ↦ c (frame i))
    (fun i ↦ c (flip (frame i))) (fun i ↦ hop _) (fun i j ↦ ⟨hp i _, hp i _⟩)
  let g (u : EuclideanSpace ℝ (Fin d)) := f (coeff u)
  have hdot (u v : EuclideanSpace ℝ (Fin d)) : T.pairing (g u) (g v) = ⟪u, v⟫_ℝ := by
    simpa only [g, hf, hgram] using (frame_inner u v).symm
  refine ⟨g, Isometry.of_dist_eq fun u v ↦ (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ?_⟩
  rw [T.dist_sq, ← T.pairing_self, ← T.pairing_self, hdot, hdot, hdot,
    dist_eq_norm, norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

theorem flat_of_corners {F X : Type*} [Field F] [MetricSpace X]
    (P : SpectralPlacementPrices F X) (hX : CATZero X) (x : Vertex d → X)
    (hx : ∀ i j, dist (x i) (x j) = dist (corner i) (corner j)) :
    Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨o, _, _, hop, hgram⟩ := tangent_frame hX x hx
  obtain ⟨g, hg⟩ := isometry_of_frame (TangentCone.coneData hX o)
    (TangentCone.catZero hX o) (fun v => TangentCone.log hX o (x v)) hop hgram
  exact ⟨(P.tangentCone hX o).pullback g hg⟩

private structure MarkedCube (d : ℕ) (F : Type*) [Field F] where
  carrier : Type
  [metric : MetricSpace carrier]
  prices : SpectralPlacementPrices F carrier
  cat : CATZero carrier
  x : Vertex d → carrier

attribute [instance] MarkedCube.metric

private theorem cube_corner_gap {F : Type*} [Field F]
    (hno : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin d)))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : MarkedCube d F, ∃ i j,
      ε ≤ |dist (p.x i) (p.x j) - dist (corner i) (corner j)| := by
  classical
  by_contra! h
  let δ (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hle (n : ℕ) : δ n ≤ 1 := by
    dsimp [δ]
    exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  choose p herr using fun n => h (δ n) (hpos n)
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let k : Vertex d := fun _ => false
  let X := fun n => (p n).carrier
  let o := fun n => (p n).x k
  let r (v : Vertex d) : Bounded U X o :=
    ⟨fun n => (p n).x v, dist (corner k) (corner v) + 1, fun n => by
      have hh := (abs_lt.mp (herr n k v)).2
      linarith only [hh, hle n]⟩
  apply hno
  apply flat_of_corners
    (SpectralPlacementPrices.metricLimit U (o := o) (fun n => (p n).prices))
    (MetricLimit.catZero (fun n => (p n).cat)) (fun v => point (r v))
  intro i j
  have ht : Tendsto (fun n => dist ((p n).x i) ((p n).x j)) atTop
      (𝓝 (dist (corner i) (corner j))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    exact squeeze_zero (fun _ => abs_nonneg _) (fun n => (herr n i j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_nhds_unique (tendsto_point_dist (r i) (r j))
    (ht.mono_left (Ultrafilter.of_le _))

/-- A single positive error excludes the d-dimensional cube in every spectral CAT(0)
space over the field, after every positive rescaling of the wire metric. -/
theorem uniform_gap {F : Type*} [Field F]
    (hno : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin d)))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (X : Type) [MetricSpace X] (_ : SpectralPlacementPrices F X),
      CATZero X → ∀ (x : Vertex d → X) (r : ℝ), 0 < r → ∃ i j,
        ε ≤ |r * dist (x i) (x j) - dist (corner i) (corner j)| := by
  obtain ⟨ε, hε, h⟩ := cube_corner_gap hno
  refine ⟨ε, hε, ?_⟩
  intro X _ P hX x r hr
  let p : MarkedCube d F := {
    carrier := MetricScale.Space r hr X
    prices := ThreeFlat.scaledSpectralPrices P (x fun _ => false) r hr
    cat := MetricScale.catZero hX
    x := fun i => ⟨x i⟩ }
  exact h p

end Hierarchy.CubeExclusion

end OAI
