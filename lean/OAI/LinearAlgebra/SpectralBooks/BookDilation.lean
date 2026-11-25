import OAI.LinearAlgebra.SpectralBooks.Book
import OAI.Geometry.HyperbolicGroups.MetricProduct

/-!
# Blowing up a bounded three-page book

The central unit ball in the spine, together with the unit depth of each
page, suffices to realize every finite configuration after shrinking by the
same factor. At integer magnifications every fixed pair of points eventually
has exactly its original distance. Thus any isometric copy of this bounded
book gives a copy of the whole book in a pointed metric ultralimit.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open Filter HyperbolicObstruction WithLp
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Multiply all heights and horizontal coordinates by the same factor. -/
def bookDilate (c : ℝ≥0) (x : Book E) : Book E :=
  toLp 2 (⟨(c : ℝ) • x.fst.val, by
    obtain ⟨i, r, hr⟩ := x.fst.property
    refine ⟨i, c * r, ?_⟩
    rw [hr]
    apply PiLp.ext
    intro j
    by_cases hj : j = i <;> simp [hj]⟩, (c : ℝ) • x.snd)

theorem bookDilate_dist (c : ℝ≥0) (x y : Book E) :
    dist (bookDilate c x) (bookDilate c y) = (c : ℝ) * dist x y := by
  have formula (a b : Book E) : dist a b =
      Real.sqrt (dist a.fst b.fst ^ 2 + dist a.snd b.snd ^ 2) := by
    rw [WithLp.prod_dist_eq_add (by norm_num : 0 < (2 : ENNReal).toReal), Real.sqrt_eq_rpow]
    norm_num
  rw [formula, formula x y]
  change Real.sqrt (dist ((c : ℝ) • x.fst.val) ((c : ℝ) • y.fst.val) ^ 2 +
    dist ((c : ℝ) • x.snd) ((c : ℝ) • y.snd) ^ 2) = _
  rw [dist_smul₀, dist_smul₀, Real.norm_eq_abs, NNReal.abs_eq, mul_pow, mul_pow, ← mul_add,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, NNReal.abs_eq]
  rfl

/-- The unit-depth slabs over the central closed unit ball in the spine. -/
def boundedBook (E : Type*) [NormedAddCommGroup E] : Set (Book E) :=
  {x | ‖x.fst.val‖ ≤ 1 ∧ ‖x.snd‖ ≤ 1}

omit [NormedSpace ℝ E] in
theorem bookPoint_mem_boundedBook (i : Fin 3) (r : ℝ≥0) (p : E) :
    bookPoint i r p ∈ boundedBook E ↔ r ≤ 1 ∧ ‖p‖ ≤ 1 := by
  change ‖PiLp.single (β := fun _ : Fin 3 => ℝ) 1 i (r : ℝ)‖ ≤ 1 ∧ ‖p‖ ≤ 1 ↔ _
  simp

/-- The common origin of the three bounded pages. -/
def boundedBookOrigin : boundedBook E :=
  ⟨bookPoint 0 0 0, (bookPoint_mem_boundedBook _ _ _).2 (by simp)⟩

private theorem bookDilate_origin (c : ℝ≥0) :
    bookDilate c (boundedBookOrigin : boundedBook E).val = boundedBookOrigin.val := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · apply Subtype.ext
    apply PiLp.ext
    intro j
    change (c : ℝ) • (PiLp.single (β := fun _ : Fin 3 => ℝ) 1 0 0 j) =
      PiLp.single (β := fun _ : Fin 3 => ℝ) 1 0 0 j
    simp
  · exact smul_zero _

private def bookShrink (n : ℕ) : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹

private theorem bookShrink_cancel (n : ℕ) : ((n : ℝ) + 1) * (bookShrink n : ℝ) = 1 := by
  simp [bookShrink, show (n : ℝ) + 1 ≠ 0 by positivity]

private theorem eventually_bookDilate_mem (x : Book E) :
    ∀ᶠ n in atTop, bookDilate (bookShrink n) x ∈ boundedBook E := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max ‖x.fst.val‖ ‖x.snd‖)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hle : max ‖x.fst.val‖ ‖x.snd‖ ≤ (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  change ‖(bookShrink n : ℝ) • x.fst.val‖ ≤ 1 ∧ ‖(bookShrink n : ℝ) • x.snd‖ ≤ 1
  simp only [norm_smul, Real.norm_eq_abs, NNReal.abs_eq]
  simp only [bookShrink, NNReal.coe_inv,
    NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, inv_mul_eq_div]
  constructor <;> apply (div_le_one (by positivity)).2
  · exact (le_max_left _ _).trans hle
  · exact (le_max_right _ _).trans hle

/-- Every finite set of book points fits into the unit slabs after one common
positive dilation. The distance law applies simultaneously to all its pairs. -/
theorem exists_bookDilate_finset (s : Finset (Book E)) :
    ∃ c : ℝ≥0, 0 < c ∧ (∀ x ∈ s, bookDilate c x ∈ boundedBook E) ∧
      ∀ x y : Book E, dist (bookDilate c x) (bookDilate c y) = (c : ℝ) * dist x y := by
  obtain ⟨n, hn⟩ := ((s.eventually_all).2 fun x _ ↦ eventually_bookDilate_mem x).exists
  exact ⟨bookShrink n, by dsimp [bookShrink]; positivity, hn, bookDilate_dist _⟩

/-- At magnification `n+1`, use the point shrunk by `1/(n+1)` whenever it
belongs to the unit slabs. The fallback affects only finitely many indices. -/
def bookApprox (n : ℕ) (x : Book E) : boundedBook E := by
  classical
  exact if h : bookDilate (bookShrink n) x ∈ boundedBook E then ⟨_, h⟩ else boundedBookOrigin

theorem eventually_bookApprox_dist (x y : Book E) :
    ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) * dist (bookApprox n x) (bookApprox n y) = dist x y := by
  filter_upwards [eventually_bookDilate_mem x, eventually_bookDilate_mem y] with n hx hy
  simp only [bookApprox, dite_eq_left hx, dite_eq_left hy, Subtype.dist_eq, bookDilate_dist, ← mul_assoc,
    bookShrink_cancel, one_mul]

private theorem bookApprox_bound (n : ℕ) (x : Book E) :
    ((n : ℝ) + 1) * dist boundedBookOrigin (bookApprox n x) ≤ dist boundedBookOrigin.val x := by
  unfold bookApprox
  split_ifs with h
  · change ((n : ℝ) + 1) * dist boundedBookOrigin.val (bookDilate (bookShrink n) x) ≤ _
    calc
      _ = ((n : ℝ) + 1) * dist (bookDilate (bookShrink n) boundedBookOrigin.val)
          (bookDilate (bookShrink n) x) := by rw [bookDilate_origin]
      _ ≤ _ := by rw [bookDilate_dist, ← mul_assoc, bookShrink_cancel, one_mul]
  · simp

/-- The ambient pointed blowup with integer magnifications about `o`. -/
abbrev IntegerBlowup {X : Type*} [MetricSpace X] (U : Ultrafilter ℕ) (o : X) :=
  MetricLimit.Space (U := U) (X := fun n ↦ MetricScale.Space ((n : ℝ) + 1) (by positivity) X)
    (o := fun _ ↦ ⟨o⟩)

/-- An isometric bounded book in an ambient space induces an isometric copy
of the entire book in its pointed blowup at the center of the spine. -/
theorem isometry_integerBlowup_of_boundedBook {X : Type*} [MetricSpace X]
    (f : boundedBook E → X) (hf : Isometry f) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ g : Book E → IntegerBlowup U (f boundedBookOrigin), Isometry g := by
  let S (x : Book E) := (show MetricLimit.Bounded U
    (fun n ↦ MetricScale.Space ((n : ℝ) + 1) (by positivity) X)
    (fun _ ↦ ⟨f boundedBookOrigin⟩) from
    ⟨fun n ↦ ⟨f (bookApprox n x)⟩, dist boundedBookOrigin.val x, fun n ↦ by
      rw [MetricScale.dist_eq, hf.dist_eq]
      exact bookApprox_bound n x⟩)
  refine ⟨fun x ↦ MetricLimit.point (S x), Isometry.of_dist_eq fun x y ↦ ?_⟩
  apply tendsto_nhds_unique (MetricLimit.tendsto_point_dist (S x) (S y))
  apply tendsto_const_nhds.congr'
  filter_upwards [(eventually_bookApprox_dist x y).filter_mono hU] with n hn
  change dist x y = ((n : ℝ) + 1) * dist (f (bookApprox n x)) (f (bookApprox n y))
  rw [hf.dist_eq]
  exact hn.symm

end

end

end SpectralBooks
end LinearAlgebra
end OAI
