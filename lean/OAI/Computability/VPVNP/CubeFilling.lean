import OAI.Computability.VPVNP.FlatRectangle
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.UnitInterval
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.SymmDiff

/-!
# Filling a Euclidean cube from its corners

The spectral wire argument uses the rigidity of flat quadrilaterals to fill an isometric
copy of the cube from its vertex configuration. We recursively interpolate
the two opposite faces. The induction keeps track of an entire family of
parallel faces, so that the diagonal distances needed for each application
of rectangle rigidity are known as well.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

open scoped unitInterval symmDiff

variable {X : Type*} [MetricSpace X]

/-- Squared Euclidean distance between two points in the unit cube. -/
def cubeSquaredDistance {n : ℕ} (x y : Fin n → I) : ℝ :=
  ∑ i, ((x i : ℝ) - y i) ^ 2

private def bitCoordinate (b : Bool) : I := if b then 1 else 0

private def bitCoordinates {n : ℕ} (u : Fin n → Bool) : Fin n → I :=
  fun i ↦ bitCoordinate (u i)

private def interpolateBits {V : Type*} (segment : V → V → I → V) :
    (n : ℕ) → ((Fin n → Bool) → V) → (Fin n → I) → V
  | 0, f, _ => f Fin.elim0
  | n + 1, f, x => segment
      (interpolateBits segment n (fun v ↦ f (Fin.cons false v)) (Fin.tail x))
      (interpolateBits segment n (fun v ↦ f (Fin.cons true v)) (Fin.tail x)) (x 0)

private noncomputable abbrev fillBits (h : HasCATZeroSegments X) :=
  interpolateBits (catPoint h)

private lemma fillBits_corners (h : HasCATZeroSegments X) (n : ℕ)
    (f : (Fin n → Bool) → X) (v : Fin n → Bool) :
    fillBits h n f (bitCoordinates v) = f v := by
  induction n with
  | zero => exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    obtain ⟨b, u, rfl⟩ := Fin.exists_cons v
    have ht : Fin.tail (bitCoordinates (Fin.cons b u)) = bitCoordinates u := by
      funext i
      simp [Fin.tail, bitCoordinates]
    dsimp only [fillBits] at ih
    rw [fillBits, interpolateBits, ht, ih, ih]
    cases b <;> simp [bitCoordinates, bitCoordinate, catPoint_zero, catPoint_one]

private theorem fillBits_sq (h : HasCATZeroSegments X) (K : ℝ) (n : ℕ)
    {J : Type*} (f : J → (Fin n → Bool) → X) (W : J → J → ℝ)
    (hzero : ∀ i, W i i = 0)
    (hf : ∀ i j u v, dist (f i u) (f j v) ^ 2 =
      W i j + K * cubeSquaredDistance (bitCoordinates u) (bitCoordinates v)) :
    ∀ i j x y, dist (fillBits h n (f i) x) (fillBits h n (f j) y) ^ 2 =
      W i j + K * cubeSquaredDistance x y := by
  induction n generalizing J with
  | zero =>
    intro i j x y
    simpa [fillBits, interpolateBits, cubeSquaredDistance] using hf i j Fin.elim0 Fin.elim0
  | succ n ih =>
    let g (p : J × Bool) (u : Fin n → Bool) := f p.1 (Fin.cons p.2 u)
    let U (p q : J × Bool) := W p.1 q.1 + K *
      ((bitCoordinate p.2 : ℝ) - bitCoordinate q.2) ^ 2
    have hU (p : J × Bool) : U p p = 0 := by simp [U, hzero]
    have hg (p q : J × Bool) (u v : Fin n → Bool) :
        dist (g p u) (g q v) ^ 2 =
          U p q + K * cubeSquaredDistance (bitCoordinates u) (bitCoordinates v) := by
      dsimp only [g]
      rw [hf]
      simp only [U, cubeSquaredDistance, Fin.sum_univ_succ, bitCoordinates, Fin.cons_zero,
        Fin.cons_succ]
      ring
    have hind := ih g U hU hg
    intro i j x y
    let a := fillBits h n (g (i, false)) (Fin.tail x)
    let b := fillBits h n (g (i, true)) (Fin.tail x)
    let d := fillBits h n (g (j, false)) (Fin.tail y)
    let c := fillBits h n (g (j, true)) (Fin.tail y)
    let T := W i j + K * cubeSquaredDistance (Fin.tail x) (Fin.tail y)
    have hab : dist a b ^ 2 = K := by
      simpa [a, b, U, hzero, bitCoordinate, cubeSquaredDistance] using
        hind (i, false) (i, true) (Fin.tail x) (Fin.tail x)
    have hdc : dist d c ^ 2 = K := by
      simpa [d, c, U, hzero, bitCoordinate, cubeSquaredDistance] using
        hind (j, false) (j, true) (Fin.tail y) (Fin.tail y)
    have had : dist a d ^ 2 = T := by
      simpa [a, d, U, T] using hind (i, false) (j, false) (Fin.tail x) (Fin.tail y)
    have hbc : dist b c ^ 2 = T := by
      simpa [b, c, U, T] using hind (i, true) (j, true) (Fin.tail x) (Fin.tail y)
    have hac : dist a c ^ 2 = K + T := by
      simpa [a, c, U, T, bitCoordinate, add_left_comm, add_assoc, add_comm] using
        hind (i, false) (j, true) (Fin.tail x) (Fin.tail y)
    have hbd : dist b d ^ 2 = K + T := by
      simpa [b, d, U, T, bitCoordinate, add_left_comm, add_assoc, add_comm] using
        hind (i, true) (j, false) (Fin.tail x) (Fin.tail y)
    change dist (catPoint h a b (x 0)) (catPoint h d c (y 0)) ^ 2 = _
    rw [rectangle_interpolate h hab hdc had hbc hac hbd]
    simp only [T, cubeSquaredDistance, Fin.sum_univ_succ, Fin.tail]
    ring

private def cornerSet {n : ℕ} (u : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ u i = true

private lemma cornerSet_distance {n : ℕ} (u v : Fin n → Bool) :
    cubeSquaredDistance (bitCoordinates u) (bitCoordinates v) =
      ((cornerSet u ∆ cornerSet v).card : ℝ) := by
  calc
    _ = ∑ i : Fin n, if i ∈ cornerSet u ∆ cornerSet v then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases hu : u i <;> cases hv : v i <;>
        simp [bitCoordinates, bitCoordinate, cornerSet, Finset.mem_symmDiff, hu, hv]
    _ = _ := by simp

/-- The corner with ones in the indicated coordinate positions. -/
def cubeCorner {n : ℕ} (A : Finset (Fin n)) (i : Fin n) : I :=
  if i ∈ A then 1 else 0

/-- The filling by successive CAT(0) segment interpolations, starting on
opposite faces and ending at the first coordinate. -/
noncomputable def fillCube (h : HasCATZeroSegments X) {n : ℕ} (f : Finset (Fin n) → X) :
    (Fin n → I) → X := fillBits h n (f ∘ cornerSet)

/-- A finite prescription for extending a set of marked parties by fractional
points. The tree depends only on the labels and fractions, so the same
prescription can be used in each subsequent metric realization. -/
inductive InterpolationTree (V : Type*) where
  | vertex (label : V)
  | segment (left right : InterpolationTree V) (fraction : I)

/-- Evaluate a finite prescription in a CAT(0) space. -/
noncomputable def InterpolationTree.eval {V : Type*} (h : HasCATZeroSegments X)
    (f : V → X) : InterpolationTree V → X
  | .vertex v => f v
  | .segment left right t => catPoint h (left.eval h f) (right.eval h f) t

private abbrev treeFromBits {V : Type*} (n : ℕ) (labels : (Fin n → Bool) → V) (x : Fin n → I) :=
  interpolateBits InterpolationTree.segment n (InterpolationTree.vertex ∘ labels) x

private theorem eval_treeFromBits {V : Type*} (h : HasCATZeroSegments X) (f : V → X)
    (n : ℕ) (labels : (Fin n → Bool) → V) (x : Fin n → I) :
    (treeFromBits n labels x).eval h f = fillBits h n (f ∘ labels) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change catPoint h ((treeFromBits n (fun v ↦ labels (Fin.cons false v)) (Fin.tail x)).eval h f)
      ((treeFromBits n (fun v ↦ labels (Fin.cons true v)) (Fin.tail x)).eval h f) (x 0) = _
    rw [ih, ih]
    rfl

/-- Interpolation instructions for a specified point of the cube, using only
the original corner labels. -/
def cubeInterpolation {n : ℕ} (x : Fin n → I) : InterpolationTree (Finset (Fin n)) :=
  treeFromBits n cornerSet x

theorem cubeInterpolation_eval (h : HasCATZeroSegments X) {n : ℕ}
    (f : Finset (Fin n) → X) (x : Fin n → I) :
    (cubeInterpolation x).eval h f = fillCube h f x :=
  eval_treeFromBits h f n cornerSet x

theorem fillCube_corner (h : HasCATZeroSegments X) {n : ℕ} (f : Finset (Fin n) → X)
    (A : Finset (Fin n)) : fillCube h f (cubeCorner A) = f A := by
  let u : Fin n → Bool := fun i ↦ decide (i ∈ A)
  have hc : bitCoordinates u = cubeCorner A := by
    funext i
    simp [bitCoordinates, bitCoordinate, cubeCorner, u]
  have hs : cornerSet u = A := by ext i; simp [cornerSet, u]
  rw [fillCube, ← hc, fillBits_corners, Function.comp_apply, hs]

/-- If the corner squared distances are scaled Hamming distances, the full
cube has Euclidean squared distances with the same scale. -/
theorem fillCube_dist_sq (h : HasCATZeroSegments X) {n : ℕ} {scale : ℝ}
    (f : Finset (Fin n) → X)
    (hf : ∀ A B, dist (f A) (f B) ^ 2 = scale ^ 2 * (A ∆ B).card)
    (x y : Fin n → I) :
    dist (fillCube h f x) (fillCube h f y) ^ 2 = scale ^ 2 * cubeSquaredDistance x y := by
  have hg (_ _ : Unit) (u v : Fin n → Bool) :
      dist ((f ∘ cornerSet) u) ((f ∘ cornerSet) v) ^ 2 =
        0 + scale ^ 2 * cubeSquaredDistance (bitCoordinates u) (bitCoordinates v) := by
    simp [cornerSet_distance, hf]
  simpa [fillCube] using fillBits_sq h (scale ^ 2) n (fun _ : Unit ↦ f ∘ cornerSet)
    (fun _ _ ↦ 0) (fun _ ↦ rfl) hg () () x y

/-- Straight line segments in the filled cube coincide with the corresponding
CAT(0) segments. In particular its image is geodesically convex. -/
theorem fillCube_segment (h : HasCATZeroSegments X) {n : ℕ} {scale : ℝ}
    (f : Finset (Fin n) → X)
    (hf : ∀ A B, dist (f A) (f B) ^ 2 = scale ^ 2 * (A ∆ B).card)
    (x y : Fin n → I) (t : I) :
    fillCube h f (fun i ↦ Set.Icc.convexComb (x i) (y i) t) =
      catPoint h (fillCube h f x) (fillCube h f y) t := by
  let z : Fin n → I := fun i ↦ Set.Icc.convexComb (x i) (y i) t
  have hx : cubeSquaredDistance z x = (t : ℝ) ^ 2 * cubeSquaredDistance x y := by
    rw [cubeSquaredDistance, cubeSquaredDistance, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [z, Set.Icc.coe_convexComb]
    ring
  have hy : cubeSquaredDistance z y = (1 - (t : ℝ)) ^ 2 * cubeSquaredDistance x y := by
    rw [cubeSquaredDistance, cubeSquaredDistance, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [z, Set.Icc.coe_convexComb]
    ring
  have hb := catPoint_bound h (fillCube h f x) (fillCube h f y) t (fillCube h f z)
  rw [fillCube_dist_sq h f hf z x, fillCube_dist_sq h f hf z y,
    fillCube_dist_sq h f hf x y, hx, hy] at hb
  apply dist_eq_zero.mp
  change dist (fillCube h f z) _ = 0
  nlinarith only [hb]

/-- The filled cube is compact. -/
theorem isCompact_range_fillCube (h : HasCATZeroSegments X) {n : ℕ} {scale : ℝ}
    (f : Finset (Fin n) → X)
    (hf : ∀ A B, dist (f A) (f B) ^ 2 = scale ^ 2 * (A ∆ B).card) :
    IsCompact (Set.range (fillCube h f)) := by
  apply isCompact_range
  rw [continuous_iff_continuous_dist]
  have he (u : (Fin n → I) × (Fin n → I)) :
      dist (fillCube h f u.1) (fillCube h f u.2) =
        Real.sqrt (scale ^ 2 * cubeSquaredDistance u.1 u.2) := by
    rw [← fillCube_dist_sq h f hf, Real.sqrt_sq dist_nonneg]
  simp_rw [he, cubeSquaredDistance]
  fun_prop

open Filter Topology in
/-- For any ambient point, a closest point in the cube satisfies the
CAT(0) projection inequality against every other point in the cube. -/
theorem fillCube_nearest (h : HasCATZeroSegments X) {n : ℕ} {scale : ℝ}
    (f : Finset (Fin n) → X)
    (hf : ∀ A B, dist (f A) (f B) ^ 2 = scale ^ 2 * (A ∆ B).card) (p : X) :
    ∃ x : Fin n → I, ∀ y : Fin n → I, dist p (fillCube h f x) ^ 2 +
      dist (fillCube h f x) (fillCube h f y) ^ 2 ≤ dist p (fillCube h f y) ^ 2 := by
  obtain ⟨q, ⟨x, rfl⟩, hmin⟩ := (isCompact_range_fillCube h f hf).exists_isMinOn
    (Set.range_nonempty _) (continuous_const.dist continuous_id).continuousOn
  refine ⟨x, fun y ↦ ?_⟩
  let q := fillCube h f x
  let v := fillCube h f y
  have bound (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1) :
      dist p q ^ 2 + (1 - r) * dist q v ^ 2 ≤ dist p v ^ 2 := by
    let t : I := ⟨r, hr.le, hr'⟩
    have hz : catPoint h q v t ∈ Set.range (fillCube h f) :=
      ⟨_, fillCube_segment h f hf x y t⟩
    have hqz : dist p q ≤ dist p (catPoint h q v t) := hmin hz
    have hsq := pow_le_pow_left₀ dist_nonneg hqz 2
    have hb := catPoint_bound h q v t p
    change dist p (catPoint h q v t) ^ 2 ≤ (1 - r) * dist p q ^ 2 +
      r * dist p v ^ 2 - r * (1 - r) * dist q v ^ 2 at hb
    apply (mul_le_mul_iff_right₀ hr).mp
    nlinarith only [hsq, hb]
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      dist p q ^ 2 + (1 - r) * dist q v ^ 2 ≤ dist p v ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)]
      with r hr hr' using bound r hr hr'.le
  have hc : Continuous (fun r : ℝ ↦ dist p q ^ 2 + (1 - r) * dist q v ^ 2) := by fun_prop
  have hlim := le_of_tendsto hc.continuousWithinAt.tendsto he
  simpa [q, v] using hlim

end SpectralGeometry

end VPVNP
end Computability
end OAI
