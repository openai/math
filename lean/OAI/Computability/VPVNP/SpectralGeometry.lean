import OAI.Computability.VPVNP.Barycenter
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Spectral wire geometry and compression estimates

In Theorem 4.2 of *VP and VNP differ over every field*, the unit cube's basis
vertices have total distance `√(j * (j - 1))` to their centroid, for a group
of size `j`. Equation (4.5) uses two such groups and charges the wire between
their centroids in proportion to its length `√(1/s + 1/t)`. Lemma 6.2 uses
the squared-distance CAT(0) inequality to reduce the weighted energy of the
six-party wire motif. Appendix A.3 obtains its endpoint-coupling bound by
splitting a two-row cost table and shrinking the range of its column gaps.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

/-- Total length of the star from the centroid to a group of basis vertices. -/
noncomputable def starLength (j : ℝ) : ℝ := Real.sqrt (j * (j - 1))

private theorem starLength_sq {j : ℝ} (hj : 1 ≤ j) :
    starLength j ^ 2 = j * (j - 1) :=
  Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))

private theorem starLength_lt {j : ℝ} (hj : 1 ≤ j) :
    starLength j < j - 1 / 2 := by
  by_contra! h
  have hs := starLength_sq hj
  have := mul_self_le_mul_self (by linarith : 0 ≤ j - 1 / 2) h
  nlinarith

/-- Splitting the star at two centroids saves strictly more than half a unit
on the terminal wires, before paying for the wire between the centroids. -/
theorem starLength_split {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    starLength s + starLength t + 1 / 2 < starLength (s + t) := by
  have h : starLength s + t < starLength (s + t) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith only [starLength_sq hs,
      mul_pos (by linarith : 0 < t) (sub_pos.mpr (starLength_lt hs))]
  linarith [starLength_lt ht]

/-- The strict gap between the star bound (4.4) and the leading term of (4.5).
The balance conditions say that each side contains at least one third of the
terminals. The inequality remains strict at the threshold `s + t = 18 * C²`. -/
theorem balancedCut_strictGap {s t C : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hbal₁ : s ≤ 2 * t) (hbal₂ : t ≤ 2 * s) (hdim : 18 * C ^ 2 ≤ s + t) :
    starLength s + starLength t + C * Real.sqrt (1 / s + 1 / t) < starLength (s + t) := by
  have hs' : 0 < s := by linarith
  have ht' : 0 < t := by linarith
  have hbudget : 4 * (C ^ 2 * (s + t)) ≤ s * t := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hbal₁) (sub_nonneg.mpr hbal₂),
      mul_nonneg (sub_nonneg.mpr hdim) (add_pos hs' ht').le]
  have hsqrt : (C * Real.sqrt (1 / s + 1 / t)) ^ 2 * (s * t) = C ^ 2 * (s + t) := by
    rw [mul_pow, Real.sq_sqrt (add_nonneg (by positivity) (by positivity))]
    field_simp
    ring
  have hsq : (C * Real.sqrt (1 / s + 1 / t)) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    apply (mul_le_mul_iff_left₀ (mul_pos hs' ht')).mp
    rw [hsqrt]
    linarith
  have hlen : C * Real.sqrt (1 / s + 1 / t) ≤ 1 / 2 := by
    by_contra! h
    have := mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) h
    nlinarith
  linarith [starLength_split hs ht]

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The centroid of the standard basis vertices indexed by a subset. -/
def subsetCentroid (S : Finset ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i ↦ if i ∈ S then (S.card : ℝ)⁻¹ else 0)

private lemma subsetCentroid_inner_self (S : Finset ι) :
    inner ℝ (subsetCentroid S) (subsetCentroid S) = (S.card : ℝ)⁻¹ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, subsetCentroid]
  change (∑ i, (if i ∈ S then (S.card : ℝ)⁻¹ else 0) *
    star (if i ∈ S then (S.card : ℝ)⁻¹ else 0)) = (S.card : ℝ)⁻¹
  simp only [star_trivial, apply_ite₂ (· * ·), zero_mul, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  by_cases hs : S.card = 0
  · simp [hs]
  · have h : (S.card : ℝ) ≠ 0 := by exact_mod_cast hs
    field_simp

/-- Distance from a standard basis vertex in a subset to that subset's centroid. -/
theorem basis_dist_subsetCentroid_sq {S : Finset ι} {i : ι} (hi : i ∈ S) :
    (dist (EuclideanSpace.single i (1 : ℝ)) (subsetCentroid S)) ^ 2 =
      1 - (S.card : ℝ)⁻¹ := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_sub_right, subsetCentroid_inner_self, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  simp [subsetCentroid, hi]

/-- Total terminal-to-centroid length of one side of the balanced layout. -/
theorem subsetCentroid_star_length (S : Finset ι) :
    ∑ i ∈ S, dist (EuclideanSpace.single i (1 : ℝ)) (subsetCentroid S) =
      √((S.card : ℝ) * ((S.card : ℝ) - 1)) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  obtain ⟨j, hj⟩ := hS
  let r := dist (EuclideanSpace.single j (1 : ℝ)) (subsetCentroid S)
  have hr : 0 ≤ r := dist_nonneg
  have hsq : r ^ 2 = 1 - (S.card : ℝ)⁻¹ := basis_dist_subsetCentroid_sq hj
  have heq (i) (hi : i ∈ S) :
      dist (EuclideanSpace.single i (1 : ℝ)) (subsetCentroid S) = r := by
    apply (sq_eq_sq₀ dist_nonneg hr).mp
    rw [basis_dist_subsetCentroid_sq hi, hsq]
  rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
  have hc : (1 : ℝ) ≤ S.card := by exact_mod_cast S.card_pos.mpr ⟨j, hj⟩
  have hc' : (S.card : ℝ) ≠ 0 := by linarith
  symm
  rw [Real.sqrt_eq_iff_eq_sq (mul_nonneg (by positivity) (sub_nonneg.mpr hc))
    (mul_nonneg (by positivity) hr), mul_pow, hsq]
  field_simp

/-- Disjoint sides of a cut have orthogonal centroids. -/
theorem disjoint_subsetCentroids_inner {S T : Finset ι} (h : Disjoint S T) :
    inner ℝ (subsetCentroid S) (subsetCentroid T) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i _
  have disj : i ∈ S → i ∉ T := fun hS hT ↦ Finset.disjoint_left.mp h hS hT
  by_cases hs : i ∈ S <;> simp [subsetCentroid, hs, disj, RCLike.inner_apply]

/-- The length of the wire joining the two side centroids in the balanced layout of (4.5). -/
theorem disjoint_subsetCentroids_dist {S T : Finset ι} (h : Disjoint S T) :
    dist (subsetCentroid S) (subsetCentroid T) =
      √((S.card : ℝ)⁻¹ + (T.card : ℝ)⁻¹) := by
  symm
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) dist_nonneg).mpr
  rw [ dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_sub_right, subsetCentroid_inner_self, subsetCentroid_inner_self,
    disjoint_subsetCentroids_inner h, disjoint_subsetCentroids_inner h.symm]
  ring


/-- Centroid of the standard basis vertices of the full cube. -/
def basisCentroid (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  subsetCentroid (Finset.univ : Finset (Fin n))

theorem basisCentroid_dist_sq {n : ℕ} (i : Fin n) :
    (dist (EuclideanSpace.single i (1 : ℝ)) (basisCentroid n)) ^ 2 = 1 - (n : ℝ)⁻¹ := by
  simpa [basisCentroid] using basis_dist_subsetCentroid_sq (Finset.mem_univ i)

theorem basisCentroid_star_length (n : ℕ) :
    ∑ i : Fin n, dist (EuclideanSpace.single i (1 : ℝ)) (basisCentroid n) =
      √((n : ℝ) * ((n : ℝ) - 1)) := by
  simpa [basisCentroid] using subsetCentroid_star_length (Finset.univ : Finset (Fin n))

private theorem equidistant_centroid_minimizes {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {x : ι → E} {c : E} {r : ℝ}
    (hr : 0 ≤ r) (hzero : ∑ i, (x i - c) = 0)
    (hrad : ∀ i, ‖x i - c‖ = r) (q : E) :
    ∑ i, dist (x i) c ≤ ∑ i, dist (x i) q := by
  simp only [dist_eq_norm, hrad]
  rcases hr.eq_or_lt with rfl | hr
  · simp only [Finset.sum_const_zero]
    exact Finset.sum_nonneg fun i _ ↦ norm_nonneg (x i - q)
  apply le_of_mul_le_mul_left _ hr
  simp only [Finset.mul_sum]
  calc
    ∑ _ : ι, r * r = ∑ i, inner ℝ (x i - c) (x i - c) := by
      simp only [real_inner_self_eq_norm_sq, hrad, sq]
    _ = ∑ i, inner ℝ (x i - c) (x i - q) := by
      have h : ∀ i, x i - q = (x i - c) + (c - q) := fun i ↦ by abel
      simp_rw [h, inner_add_right]
      rw [Finset.sum_add_distrib, ← sum_inner, hzero, inner_zero_left, add_zero]
    _ ≤ ∑ i, r * ‖x i - q‖ := Finset.sum_le_sum fun i _ ↦ by
      simpa only [hrad] using real_inner_le_norm (x i - c) (x i - q)

private theorem basisCentroid_sum_sub (n : ℕ) :
    ∑ i : Fin n, (EuclideanSpace.single i (1 : ℝ) - basisCentroid n) = 0 := by
  ext j
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.pos)
  change (WithLp.ofLp (∑ i : Fin n, (EuclideanSpace.single i (1 : ℝ) - basisCentroid n))) j = 0
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_sub, Pi.sub_apply, EuclideanSpace.single, PiLp.ofLp_single, Pi.single_apply,
    basisCentroid, subsetCentroid, Finset.sum_sub_distrib]
  simp [hn]

/-- Among all centers, the centroid minimizes the total distance to the basis vertices. -/
theorem basisCentroid_minimizes {n : ℕ} (q : EuclideanSpace ℝ (Fin n)) :
    ∑ i : Fin n, dist (EuclideanSpace.single i (1 : ℝ)) (basisCentroid n) ≤
      ∑ i : Fin n, dist (EuclideanSpace.single i (1 : ℝ)) q := by
  refine equidistant_centroid_minimizes (r := √(1 - (n : ℝ)⁻¹))
    (Real.sqrt_nonneg _) (basisCentroid_sum_sub n) ?_ q
  intro i
  rw [← basisCentroid_dist_sq i, Real.sqrt_sq (dist_nonneg), dist_eq_norm]


/-- A balanced two-centroid layout has strictly less total weighted wire length
than the single-center layout, for every choice of the single center. The
terminal wires have unit cost and the wire between centroids has weight `C`. -/
theorem balancedLayout_strict {n : ℕ} {C : ℝ} (hC : 1 ≤ C) (hdim : 18 * C ^ 2 ≤ n)
    (S : Finset (Fin n)) (hlo : n ≤ 3 * S.card) (hhi : 3 * S.card ≤ 2 * n)
    (q : EuclideanSpace ℝ (Fin n)) :
    (∑ i ∈ S, dist (EuclideanSpace.single i (1 : ℝ)) (subsetCentroid S)) +
      (∑ i ∈ Sᶜ, dist (EuclideanSpace.single i (1 : ℝ)) (subsetCentroid Sᶜ)) +
      C * dist (subsetCentroid S) (subsetCentroid Sᶜ) <
      ∑ i : Fin n, dist (EuclideanSpace.single i (1 : ℝ)) q := by
  have hnR : (1 : ℝ) ≤ n := by nlinarith only [sq_nonneg (C - 1), hC, hdim]
  have hn : 1 ≤ n := by exact_mod_cast hnR
  have hsum : S.card + Sᶜ.card = n := by simp
  have hs : 1 ≤ S.card := by omega
  have ht : 1 ≤ Sᶜ.card := by omega
  have hbal₁ : S.card ≤ 2 * Sᶜ.card := by omega
  have hbal₂ : Sᶜ.card ≤ 2 * S.card := by omega
  have hsumR : (S.card : ℝ) + (Sᶜ.card : ℝ) = n := by exact_mod_cast hsum
  have hgap := balancedCut_strictGap (C := C) (s := (S.card : ℝ)) (t := (Sᶜ.card : ℝ))
    (by exact_mod_cast hs) (by exact_mod_cast ht) (by exact_mod_cast hbal₁)
    (by exact_mod_cast hbal₂) (hsumR ▸ hdim)
  apply lt_of_lt_of_le _ (basisCentroid_minimizes q)
  rw [subsetCentroid_star_length, subsetCentroid_star_length,
    disjoint_subsetCentroids_dist disjoint_compl_right, basisCentroid_star_length]
  simpa only [hsumR, starLength, one_div] using hgap

end

/-- Lemma 6.2. The two demand edges are `ab` and `cd`. Each group of four
supply edges receives masses `8/31, 4/31, 40/93, 16/31`, totaling `4/3`. -/
theorem sixParty_energy {X : Type*} [PseudoMetricSpace X] (h : HasCATZeroSegments X)
    (a b c d m n : X) :
    (1 / 3 : ℝ) * dist a b ^ 2 + dist c d ^ 2 ≤
      (31 / 16 : ℝ) * ((8 / 31 : ℝ) * (dist a c ^ 2 + dist b c ^ 2) +
        (4 / 31 : ℝ) * (dist a m ^ 2 + dist b n ^ 2) +
        (40 / 93 : ℝ) * (dist c m ^ 2 + dist c n ^ 2) +
        (16 / 31 : ℝ) * (dist d m ^ 2 + dist d n ^ 2)) := by
  obtain ⟨u, hu⟩ := h c m (1 / 3) (by norm_num) (by norm_num)
  obtain ⟨v, hv⟩ := h c n (1 / 3) (by norm_num) (by norm_num)
  obtain ⟨o, ho⟩ := h m n (1 / 2) (by norm_num) (by norm_num)
  -- The two one-third points satisfy the common-origin convexity estimate.
  have hcu := hu c
  rw [dist_self] at hcu
  have hnu := hu n
  rw [dist_comm n c, dist_comm n m, dist_comm n u] at hnu
  have huv := hv u
  rw [dist_comm u c] at huv
  have huv_le : dist u v ≤ (1 / 3 : ℝ) * dist m n := by
    apply (sq_le_sq₀ dist_nonneg (by positivity)).1
    linarith only [hcu, hnu, huv]
  have hab : dist a b ≤ dist a u + dist b v + dist m n / 3 := by
    have hpath := dist_triangle4 a u v b
    rw [dist_comm v b] at hpath
    linarith
  have hab_sq := (sq_le_sq₀ dist_nonneg (by positivity)).2 hab
  have hab_energy : (1 / 3 : ℝ) * dist a b ^ 2 ≤
      (3 / 4 : ℝ) * (dist a u ^ 2 + dist b v ^ 2) + dist m n ^ 2 := by
    nlinarith only [hab_sq, sq_nonneg (dist a u - dist b v),
      sq_nonneg (dist a u - 4 * dist m n), sq_nonneg (dist b v - 4 * dist m n),
      sq_nonneg (dist a u), sq_nonneg (dist b v), sq_nonneg (dist m n)]
  have hcd_sq := (sq_le_sq₀ dist_nonneg (by positivity)).2 (dist_triangle_right c d o)
  have hcd_energy : dist c d ^ 2 ≤ 2 * (dist c o ^ 2 + dist d o ^ 2) := by
    nlinarith only [hcd_sq, sq_nonneg (dist c o - dist d o)]
  linarith only [hab_energy, hcd_energy, hu a, hv b, ho c, ho d]

/-- A table on the endpoint choices of two intervals. `false` denotes the first endpoint. -/
abbrev EndpointTable := Bool → Bool → ℝ

/-- The difference between the two rows in column `j`. -/
def columnGap (M : EndpointTable) (j : Bool) : ℝ := M false j - M true j

/-- With two columns the midpoint between the maximum and minimum gap is their average. -/
noncomputable def gapMidpoint (M : EndpointTable) : ℝ := (columnGap M false + columnGap M true) / 2

/-- The `true` branch is the positive split and lowers entries of row zero. The negative
split lowers entries of row one. -/
noncomputable def splitTable (M : EndpointTable) : Bool → EndpointTable
  | true, false, j => min (M false j) (M true j + gapMidpoint M)
  | true, true, j => M true j
  | false, false, j => M false j
  | false, true, j => min (M true j) (M false j - gapMidpoint M)

theorem splitTable_le (M : EndpointTable) (branch i j : Bool) :
    splitTable M branch i j ≤ M i j := by
  cases branch <;> cases i <;> simp [splitTable]

theorem columnGap_split (M : EndpointTable) (branch j : Bool) :
    columnGap (splitTable M branch) j = if branch then min (columnGap M j) (gapMidpoint M)
      else max (columnGap M j) (gapMidpoint M) := by
  cases branch
  · simp only [columnGap, splitTable, Bool.false_eq_true, ↓reduceIte, ← max_sub_sub_left,
      sub_sub_cancel]
  · simp only [columnGap, splitTable, ↓reduceIte, ← min_sub_sub_right, add_sub_cancel_left]

theorem splitTable_gapDifference (M : EndpointTable) (branch : Bool) :
    columnGap (splitTable M branch) false - columnGap (splitTable M branch) true =
      (columnGap M false - columnGap M true) / 2 := by
  have hmid : ∀ a b : ℝ, a ≤ b → a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b := by
    intro a b hab
    constructor <;> linarith
  rcases le_total (columnGap M false) (columnGap M true) with hab | hba
  · obtain ⟨ha, hb⟩ := hmid _ _ hab
    cases branch <;> simp [columnGap_split, gapMidpoint, ha, hb] <;> ring
  · have ha : (columnGap M false + columnGap M true) / 2 ≤ columnGap M false := by linarith
    have hb : columnGap M true ≤ (columnGap M false + columnGap M true) / 2 := by linarith
    cases branch <;> simp [columnGap_split, gapMidpoint, ha, hb] <;> ring

/-- Follow the specified sequence of positive and negative splits from the root table. -/
noncomputable def leafTable (M : EndpointTable) : List Bool → EndpointTable
  | [] => M
  | branch :: rest => leafTable (splitTable M branch) rest

theorem leafTable_le (M : EndpointTable) (path : List Bool) (i j : Bool) :
    leafTable M path i j ≤ M i j := by
  induction path generalizing M with
  | nil => rfl
  | cons branch rest ih => exact (ih (splitTable M branch)).trans (splitTable_le M branch i j)

/-- At a leaf the difference of the two column gaps is exactly the initial difference
multiplied by one half per split. -/
theorem leafTable_gapDifference (M : EndpointTable) (path : List Bool) :
    columnGap (leafTable M path) false - columnGap (leafTable M path) true =
      (columnGap M false - columnGap M true) * (1 / 2) ^ path.length := by
  induction path generalizing M with
  | nil => simp [leafTable]
  | cons branch rest ih =>
    rw [leafTable, ih, splitTable_gapDifference, List.length_cons, pow_succ]
    ring

/-- The gap in each column stays in the initial interval at every stage. -/
theorem leafTable_columnGap_mem (M : EndpointTable) (path : List Bool) {t : ℝ}
    (h : ∀ j, |columnGap M j| ≤ t) (j : Bool) : |columnGap (leafTable M path) j| ≤ t := by
  induction path generalizing M with
  | nil => exact h j
  | cons branch rest ih =>
    apply ih
    intro k
    have h₀ := abs_le.mp (h false)
    have h₁ := abs_le.mp (h true)
    have hmid : -t ≤ gapMidpoint M ∧ gapMidpoint M ≤ t := by
      unfold gapMidpoint
      constructor <;> linarith
    have hk := abs_le.mp (h k)
    rw [columnGap_split, abs_le]
    cases branch <;> simp [hk.1, hk.2, hmid.1, hmid.2]

/-- A joint distribution with endpoint marginals `(1-u,u)` and `(1-v,v)`. -/
structure EndpointCoupling (u v : ℝ) where
  /-- Joint mass at each pair of endpoints, with row and column sums prescribed by the two
  interpolation parameters. -/
  mass : EndpointTable
  nonneg : ∀ i j, 0 ≤ mass i j
  row₀ : mass false false + mass false true = 1 - u
  row₁ : mass true false + mass true true = u
  col₀ : mass false false + mass true false = 1 - v
  col₁ : mass false true + mass true true = v

/-- Independent choices of the two endpoints. -/
noncomputable def independentCoupling {u v : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) :
    EndpointCoupling u v where
  mass i j := (if i then u else 1 - u) * (if j then v else 1 - v)
  nonneg i j := by
    cases i <;> cases j <;> simp <;> exact mul_nonneg (by linarith) (by linarith)
  row₀ := by simp; ring
  row₁ := by simp; ring
  col₀ := by simp; ring
  col₁ := by simp; ring

/-- Expected value of the four entries under the coupling. -/
noncomputable def EndpointCoupling.cost {u v : ℝ} (π : EndpointCoupling u v) (M : EndpointTable) : ℝ :=
  π.mass false false * M false false + π.mass false true * M false true +
  π.mass true false * M true false + π.mass true true * M true true

private theorem coupling_mass₀_le_one {u v : ℝ} (π : EndpointCoupling u v) :
    π.mass false false ≤ 1 := by
  linarith only [π.row₀, π.row₁, π.nonneg false true, π.nonneg true false, π.nonneg true true]

/-- Equal marginals force the signed difference of joint masses to be a multiple of the
alternating table. Only the difference of the two column gaps contributes to its cost. -/
theorem coupling_cost_sub {u v : ℝ} (ρ π : EndpointCoupling u v) (M : EndpointTable) :
    ρ.cost M - π.cost M = (ρ.mass false false - π.mass false false) *
      (columnGap M false - columnGap M true) := by
  let e := ρ.mass false false - π.mass false false
  have h₀₁ : ρ.mass false true = π.mass false true - e := by dsimp [e]; linarith only [ρ.row₀, π.row₀]
  have h₁₀ : ρ.mass true false = π.mass true false - e := by dsimp [e]; linarith only [ρ.col₀, π.col₀]
  have h₁₁ : ρ.mass true true = π.mass true true + e := by linarith only [ρ.row₁, π.row₁, h₁₀]
  simp only [EndpointCoupling.cost, columnGap, h₀₁, h₁₀, h₁₁, e]
  ring

/-- The scalar coupling estimate at depth `path.length` in Appendix A.3. In particular
`ρ` can be the independent coupling, while `π` may be any coupling of the endpoints. -/
theorem coupling_leaf_bound {u v t : ℝ} (ρ π : EndpointCoupling u v)
    (M : EndpointTable) (h : ∀ j, |columnGap M j| ≤ t) (path : List Bool) :
    ρ.cost (leafTable M path) ≤ π.cost M + 2 * t * (1 / 2) ^ path.length := by
  have hmass : |ρ.mass false false - π.mass false false| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith only [coupling_mass₀_le_one π, coupling_mass₀_le_one ρ,
      π.nonneg false false, ρ.nonneg false false]
  have hgap : |columnGap M false - columnGap M true| ≤ 2 * t := by
    exact (abs_sub _ _).trans (by linarith only [h false, h true])
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ path.length := by positivity
  have hleaf : π.cost (leafTable M path) ≤ π.cost M := by
    have hw (i j : Bool) := mul_le_mul_of_nonneg_left (leafTable_le M path i j) (π.nonneg i j)
    unfold EndpointCoupling.cost
    linarith only [hw false false, hw false true, hw true false, hw true true]
  have habs : |ρ.cost (leafTable M path) - π.cost (leafTable M path)| ≤
      2 * t * (1 / 2) ^ path.length := by
    rw [coupling_cost_sub, leafTable_gapDifference, abs_mul, abs_mul, abs_of_nonneg hpow]
    calc _ ≤ 1 * (2 * t * (1 / 2) ^ path.length) :=
            mul_le_mul hmass (mul_le_mul_of_nonneg_right hgap hpow) (by positivity) (by norm_num)
         _ = _ := one_mul _
  linarith only [hleaf, (le_abs_self _).trans habs]

end SpectralGeometry

end VPVNP
end Computability
end OAI
