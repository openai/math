import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rational width grids for a fixed wire motif

In Theorem 6.1 of *VP and VNP differ over every field*, the spectral distances
on the demand and supply edges obey a weighted quadratic inequality. The
width grids below work simultaneously for every distance pattern satisfying
that inequality. All entries have one common denominator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifGrid

open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- Width norm for edges with positive masses `p`. -/
noncomputable def widthNorm (p x : I → ℝ) : ℝ := √(∑ i, x i ^ 2 / p i)

/-- Squared distance in the dual weighted norm. -/
noncomputable def distanceEnergy (p d : I → ℝ) : ℝ := ∑ i, p i * d i ^ 2

/-- Logarithmic spectral value of a collection of wires. -/
noncomputable def wireValue (x d : I → ℝ) : ℝ := ∑ i, x i * d i

/-- Weighted Cauchy–Schwarz for the primal width norm and dual distance norm. -/
theorem wireValue_le (p x d : I → ℝ) (hp : ∀ i, 0 < p i) :
    wireValue x d ≤ widthNorm p x * √(distanceEnergy p d) := by
  have hroot (i : I) : 0 < √(p i) := Real.sqrt_pos.mpr (hp i)
  have cross (i : I) : x i / √(p i) * (√(p i) * d i) = x i * d i := by
    field_simp [(hroot i).ne']
  have left (i : I) : (x i / √(p i)) ^ 2 = x i ^ 2 / p i := by
    rw [div_pow, Real.sq_sqrt (hp i).le]
  have right (i : I) : (√(p i) * d i) ^ 2 = p i * d i ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hp i).le]
  simpa only [wireValue, widthNorm, distanceEnergy, cross, left, right] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i ↦ x i / √(p i)) (fun i ↦ √(p i) * d i)

/-- Squaring the width norm recovers its weighted energy. -/
theorem norm_sq (p x : I → ℝ) (hp : ∀ i, 0 < p i) :
    widthNorm p x ^ 2 = ∑ i, x i ^ 2 / p i :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ div_nonneg (sq_nonneg _) (hp i).le)

/-- A single edge contributes at most the full width norm. -/
theorem coordinate_le (p x : I → ℝ) (hp : ∀ i, 0 < p i) (i : I) :
    x i ≤ √(p i) * widthNorm p x := by
  have h := Finset.single_le_sum (f := fun j ↦ x j ^ 2 / p j)
    (fun j _ ↦ div_nonneg (sq_nonneg _) (hp j).le) (Finset.mem_univ i)
  rw [← norm_sq _ _ hp] at h
  have hle := (div_le_iff₀ (hp i)).mp h
  have hsq : (√(p i) * widthNorm p x) ^ 2 = p i * widthNorm p x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hp i).le]
  by_contra! hlt
  have hpos : 0 ≤ √(p i) * widthNorm p x := mul_nonneg (Real.sqrt_nonneg (p i)) (Real.sqrt_nonneg _)
  nlinarith only [hsq, hle, mul_self_lt_mul_self hpos hlt]

private theorem wireValue_mono (x y d : I → ℝ) (hxy : ∀ i, x i ≤ y i)
    (hd : ∀ i, 0 ≤ d i) : wireValue x d ≤ wireValue y d :=
  Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hxy i) (hd i)

/-- The width norm is monotone on nonnegative widths. -/
theorem norm_mono (p x y : I → ℝ) (hp : ∀ i, 0 < p i)
    (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) : widthNorm p x ≤ widthNorm p y :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ ↦ div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (hx i) (hxy i) _) (hp i).le)

private theorem add_error_value (x d : I → ℝ) (ε : ℝ) :
    wireValue (fun i ↦ x i + ε) d = wireValue x d + ε * wireValue (fun _ ↦ 1) d := by
  simp [wireValue, add_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- Coordinatewise upward rounding by at most `ε` increases the norm by at most
`ε` times the width norm of the all-ones vector. -/
theorem widthNorm_round_le (p x z : I → ℝ) (hp : ∀ i, 0 < p i) {ε : ℝ} (hε : 0 ≤ ε)
    (hz : ∀ i, 0 ≤ z i) (hxz : ∀ i, z i ≤ x i + ε) :
    widthNorm p z ≤ widthNorm p x + ε * widthNorm p (fun _ ↦ 1) := by
  let d := fun i ↦ z i / p i
  have hd i : 0 ≤ d i := div_nonneg (hz i) (hp i).le
  have henergy : √(distanceEnergy p d) = widthNorm p z := by
    unfold distanceEnergy widthNorm
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [d]
    field_simp [(hp i).ne']
  have hval : wireValue z d = widthNorm p z ^ 2 := by
    rw [norm_sq _ _ hp]
    unfold wireValue
    apply Finset.sum_congr rfl
    intro i _
    dsimp [d]
    ring
  have hr := wireValue_mono z (fun i ↦ x i + ε) d hxz hd
  rw [hval, add_error_value] at hr
  have hx := wireValue_le p x d hp
  have h1 := wireValue_le p (fun _ ↦ 1) d hp
  rw [henergy] at hx h1
  by_cases hzero : widthNorm p z = 0
  · rw [hzero]
    exact add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hε (Real.sqrt_nonneg _))
  · have hpos : 0 < widthNorm p z := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hzero)
    apply (le_of_mul_le_mul_right _ hpos)
    nlinarith only [hr, hx, mul_le_mul_of_nonneg_left h1 hε]

/-- One finite box of vectors on a common rational mesh. -/
private noncomputable def boxGrid (B : ℕ) (K : I → ℝ) : Finset (I → ℚ) := by
  classical
  exact Finset.univ.image (fun f : (i : I) → Fin (⌈(B : ℝ) * K i⌉₊ + 1) ↦
    fun i ↦ (f i).val / (B : ℚ))

private theorem zero_mem_boxGrid (B : ℕ) (K : I → ℝ) : (fun _ ↦ 0) ∈ boxGrid B K := by
  classical
  refine Finset.mem_image.mpr ⟨fun _ ↦ 0, Finset.mem_univ _, ?_⟩
  ext i
  simp

private theorem boxGrid_nonneg {B : ℕ} {K : I → ℝ} {r : I → ℚ} (hr : r ∈ boxGrid B K) :
    ∀ i, 0 ≤ r i := by
  classical
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hr
  intro i
  dsimp
  positivity

private theorem boxGrid_integral {B : ℕ} {K : I → ℝ} {r : I → ℚ} (hr : r ∈ boxGrid B K) :
    ∃ k : I → ℕ, ∀ i, r i = (k i : ℚ) / B := by
  classical
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hr
  exact ⟨fun i ↦ (f i).val, fun _ ↦ rfl⟩

private theorem round_box {B : ℕ} (hB : (0 : ℝ) < B) (K x : I → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hK : ∀ i, x i ≤ K i) :
    ∃ u ∈ boxGrid B K, ∃ l ∈ boxGrid B K, ∀ i,
      (x i ≤ (u i : ℝ) ∧ (u i : ℝ) ≤ x i + 1 / B) ∧
      ((l i : ℝ) ≤ x i ∧ x i ≤ (l i : ℝ) + 1 / B) := by
  classical
  let k := fun i ↦ (B : ℝ) * x i
  have hcap i : ⌈k i⌉₊ ≤ ⌈(B : ℝ) * K i⌉₊ := Nat.ceil_mono (mul_le_mul_of_nonneg_left (hK i) hB.le)
  let u := fun i ↦ (⟨⌈k i⌉₊, Nat.lt_succ_of_le (hcap i)⟩ : Fin (⌈(B : ℝ) * K i⌉₊ + 1))
  let l := fun i ↦ (⟨⌊k i⌋₊, Nat.lt_succ_of_le ((Nat.floor_le_ceil _).trans (hcap i))⟩ :
    Fin (⌈(B : ℝ) * K i⌉₊ + 1))
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ u),
    _, Finset.mem_image_of_mem _ (Finset.mem_univ l), ?_⟩
  intro i
  have hk : 0 ≤ k i := mul_nonneg hB.le (hx i)
  simp only [u, l, Rat.cast_div, Rat.cast_natCast, ← add_div]
  constructor
  · constructor
    · exact (le_div_iff₀ hB).mpr (by simpa [k, mul_comm] using Nat.le_ceil (k i))
    · apply (div_le_iff₀ hB).mpr
      have := Nat.ceil_lt_add_one hk
      dsimp [k] at this ⊢
      rw [add_mul, div_mul_cancel₀ _ hB.ne']
      linarith
  · constructor
    · exact (div_le_iff₀ hB).mpr (by simpa [k, mul_comm] using Nat.floor_le hk)
    · exact (le_div_iff₀ hB).mpr (by simpa [k, mul_comm] using (Nat.lt_floor_add_one (k i)).le)

/-- Optimal supply widths at dual distances `d`. -/
private noncomputable def maximizer (q d : I → ℝ) (R : ℝ) : I → ℝ :=
  fun i ↦ (R / √(distanceEnergy q d)) * (q i * d i)

private theorem maximizer_value (q d : I → ℝ) (R : ℝ) (hE : 0 < distanceEnergy q d) :
    wireValue (maximizer q d R) d = R * √(distanceEnergy q d) := by
  have he := Real.sq_sqrt hE.le
  have hs := (Real.sqrt_pos.mpr hE).ne'
  calc
    _ = R / √(distanceEnergy q d) * distanceEnergy q d := by
      unfold wireValue maximizer distanceEnergy
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = R / √(distanceEnergy q d) * (√(distanceEnergy q d)) ^ 2 := by rw [he]
    _ = _ := by field_simp [hs]

private theorem maximizer_norm (q d : I → ℝ) (hq : ∀ i, 0 < q i) {R : ℝ} (hR : 0 ≤ R)
    (hE : 0 < distanceEnergy q d) : widthNorm q (maximizer q d R) = R := by
  have hsq : widthNorm q (maximizer q d R) ^ 2 = R ^ 2 := by
    rw [norm_sq _ _ hq]
    calc
      _ = (R / √(distanceEnergy q d)) ^ 2 * distanceEnergy q d := by
        rw [show (R / √(distanceEnergy q d)) ^ 2 * distanceEnergy q d =
          ∑ i, (R / √(distanceEnergy q d)) ^ 2 * (q i * d i ^ 2) by
            unfold distanceEnergy; rw [Finset.mul_sum]]
        apply Finset.sum_congr rfl
        intro i _
        unfold maximizer
        rw [mul_pow, mul_pow]
        field_simp [(hq i).ne']
      _ = _ := by rw [div_pow, Real.sq_sqrt hE.le, div_mul_cancel₀ _ hE.ne']
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | hneg
  · exact heq
  · have hnorm : 0 ≤ widthNorm q (maximizer q d R) := Real.sqrt_nonneg _
    linarith

/-- Cast a rational width vector into the real weighted space. -/
def realWidths (z : I → ℚ) : I → ℝ := fun i ↦ z i

private theorem zero_norm (m : I → ℝ) : widthNorm m (realWidths (fun _ ↦ 0)) = 0 :=
  by simp [realWidths, widthNorm]

variable {D S : Type*} [Fintype D] [Fintype S]

/-- The two finite grids, their common denominator, and their approximation and
comparison properties. The supply witness may depend on the spectral point. -/
structure StrictGrids (p : D → ℝ) (q : S → ℝ) (H R : ℝ) where
  /-- Positive integer giving the common mesh size through its reciprocal on both rational
  grids. -/
  denominator : ℕ
  denominator_pos : 0 < denominator
  /-- Finite rational demand-width vectors that cover every nonnegative demand of weighted norm
  at most one by coordinatewise rounding up. -/
  demands : Finset (D → ℚ)
  /-- Finite rational supply-width vectors of weighted norm at most the supply radius, among
  which strict domination is witnessed. -/
  supplies : Finset (S → ℚ)
  zero_mem_demands : (fun _ ↦ 0) ∈ demands
  zero_mem_supplies : (fun _ ↦ 0) ∈ supplies
  demand_integral : ∀ z ∈ demands, ∃ k : D → ℕ, ∀ i, z i = (k i : ℚ) / denominator
  supply_integral : ∀ w ∈ supplies, ∃ k : S → ℕ, ∀ i, w i = (k i : ℚ) / denominator
  slack : (1 + (1 / denominator : ℝ) * widthNorm p (fun _ ↦ 1)) * √H +
    (1 / denominator : ℝ) * widthNorm q (fun _ ↦ 1) < R
  demand_norm : ∀ z ∈ demands, widthNorm p (realWidths z) ≤
    1 + (1 / denominator : ℝ) * widthNorm p (fun _ ↦ 1)
  supply_norm : ∀ w ∈ supplies, widthNorm q (realWidths w) ≤ R
  cover : ∀ x : D → ℝ, (∀ i, 0 ≤ x i) → widthNorm p x ≤ 1 →
    ∃ z ∈ demands, ∀ i, x i ≤ z i ∧ (z i : ℝ) ≤ x i + 1 / denominator
  strict : ∀ z ∈ demands, ∀ (d : D → ℝ) (e : S → ℝ), (∀ i, 0 ≤ e i) →
    0 < distanceEnergy q e → distanceEnergy p d ≤ H * distanceEnergy q e →
    ∃ w ∈ supplies, wireValue (realWidths z) d < wireValue (realWidths w) e

/-- Uniform finite rational approximation in the first part of Theorem 6.1.
The grid is independent of the demand widths and of the spectral point. -/
theorem exists_strict_grids (p : D → ℝ) (q : S → ℝ) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, 0 < q i) {H R : ℝ} (hH : 0 ≤ H) (hR : √H < R) : Nonempty (StrictGrids p q H R) := by
  classical
  let P := widthNorm p (fun _ ↦ 1)
  let Q := widthNorm q (fun _ ↦ 1)
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hgap : 0 < R - √H := sub_pos.mpr hR
  obtain ⟨B, hB⟩ := exists_nat_gt ((√H * P + Q) / (R - √H))
  have hpos : (0 : ℝ) < B := (div_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hP) hQ)
    hgap.le).trans_lt hB
  let ε : ℝ := 1 / B
  have hε : 0 ≤ ε := div_nonneg zero_le_one hpos.le
  have hslack : (1 + ε * P) * √H + ε * Q < R := by
    have ht : (√H * P + Q) / B < R - √H := (div_lt_iff₀ hpos).mpr (by
      linarith only [(div_lt_iff₀ hgap).mp hB])
    dsimp [ε]
    rw [show (1 + 1 / (B : ℝ) * P) * √H + 1 / B * Q = √H + (√H * P + Q) / B by ring]
    linarith
  let Z := (boxGrid B (fun i ↦ √(p i))).filter fun z ↦ widthNorm p (realWidths z) ≤ 1 + ε * P
  let W := (boxGrid B (fun i ↦ √(q i) * R)).filter fun w ↦ widthNorm q (realWidths w) ≤ R
  refine ⟨⟨B, Nat.cast_pos.mp hpos, Z, W,
    Finset.mem_filter.mpr ⟨zero_mem_boxGrid _ _, (zero_norm _).trans_le
      (add_nonneg zero_le_one (mul_nonneg hε hP))⟩,
    Finset.mem_filter.mpr ⟨zero_mem_boxGrid _ _,
      (zero_norm _).trans_le ((Real.sqrt_nonneg H).trans hR.le)⟩,
    fun _ hz ↦ boxGrid_integral (Finset.mem_filter.mp hz).1,
    fun _ hw ↦ boxGrid_integral (Finset.mem_filter.mp hw).1, hslack,
    fun _ hz ↦ (Finset.mem_filter.mp hz).2, fun _ hw ↦ (Finset.mem_filter.mp hw).2, ?_, ?_⟩⟩
  · intro x hx hnorm
    have hcap i : x i ≤ √(p i) := (coordinate_le p x hp i).trans <| by
      simpa using mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg (p i))
    obtain ⟨z, hz, _, _, happrox⟩ := round_box hpos _ x hx hcap
    refine ⟨z, Finset.mem_filter.mpr ⟨hz, ?_⟩, fun i ↦ (happrox i).1⟩
    have hz0 i : 0 ≤ realWidths z i := Rat.cast_nonneg.mpr (boxGrid_nonneg hz i)
    exact (widthNorm_round_le p x _ hp hε hz0 (fun i ↦ (happrox i).1.2)).trans
      (add_le_add_left hnorm _)
  · intro z hz d e he hE hcomp
    let wstar := maximizer q e R
    have hR0 := (Real.sqrt_nonneg H).trans hR.le
    have hw i : 0 ≤ wstar i := mul_nonneg (div_nonneg hR0 (Real.sqrt_nonneg _))
      (mul_nonneg (hq i).le (he i))
    have hnorm : widthNorm q wstar = R := maximizer_norm q e hq hR0 hE
    have hcap i : wstar i ≤ √(q i) * R := by simpa [hnorm] using coordinate_le q wstar hq i
    obtain ⟨_, _, w, hwmem, happrox⟩ := round_box hpos _ wstar hw hcap
    have hw0 i : 0 ≤ realWidths w i := Rat.cast_nonneg.mpr (boxGrid_nonneg hwmem i)
    refine ⟨w, Finset.mem_filter.mpr ⟨hwmem, (norm_mono q _ _ hq hw0
      (fun i ↦ (happrox i).2.1)).trans hnorm.le⟩, ?_⟩
    let L := √(distanceEnergy q e)
    have hL : 0 < L := Real.sqrt_pos.mpr hE
    have hdual : √(distanceEnergy p d) ≤ √H * L := by
      rw [← Real.sqrt_mul hH]; exact Real.sqrt_le_sqrt hcomp
    have hzbound : widthNorm p (realWidths z) ≤ 1 + ε * P := (Finset.mem_filter.mp hz).2
    have hzvalue : wireValue (realWidths z) d ≤ (1 + ε * P) * (√H * L) :=
      (wireValue_le _ _ _ hp).trans (mul_le_mul hzbound hdual (Real.sqrt_nonneg _)
        (add_nonneg zero_le_one (mul_nonneg hε hP)))
    have hwvalue := wireValue_mono wstar (fun i ↦ realWidths w i + ε) e
      (fun i ↦ (happrox i).2.2) he
    rw [add_error_value, show wireValue wstar e = R * L from maximizer_value q e R hE] at hwvalue
    have hones := wireValue_le q (fun _ ↦ 1) e hq
    change wireValue (fun _ ↦ 1) e ≤ Q * L at hones
    nlinarith only [hzvalue, hwvalue, mul_le_mul_of_nonneg_left hones hε,
      mul_lt_mul_of_pos_right hslack hL]

/-- Scaling all widths by a nonnegative factor scales their norm by that factor. -/
theorem widthNorm_scale (p x : I → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    widthNorm p (fun i ↦ a * x i) = a * widthNorm p x := by
  unfold widthNorm
  simp_rw [mul_pow, mul_div_assoc]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

/-- Scaling all widths scales the logarithmic wire value. -/
theorem wireValue_scale (x d : I → ℝ) (a : ℝ) :
    wireValue (fun i ↦ a * x i) d = a * wireValue x d := by
  simp [wireValue, Finset.mul_sum, mul_assoc]

namespace StrictGrids

variable {p : D → ℝ} {q : S → ℝ} {H R : ℝ} (G : StrictGrids p q H R)

/-- Demand bit widths when the base scale is `t * G.denominator`. -/
noncomputable def demandWidths (t : ℕ) (z : G.demands) (i : D) : ℕ :=
  t * (G.demand_integral _ z.property).choose i

/-- Supply bit widths on the same base scale. -/
noncomputable def supplyWidths (t : ℕ) (w : G.supplies) (i : S) : ℕ :=
  t * (G.supply_integral _ w.property).choose i

@[simp] theorem cast_demandWidths (t : ℕ) (z : G.demands) (i : D) :
    (G.demandWidths t z i : ℝ) = ((t * G.denominator : ℕ) : ℝ) * (z.val i : ℝ) := by
  rw [(G.demand_integral _ z.property).choose_spec i]
  unfold demandWidths
  push_cast
  field_simp [show (G.denominator : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr G.denominator_pos.ne']

@[simp] theorem cast_supplyWidths (t : ℕ) (w : G.supplies) (i : S) :
    (G.supplyWidths t w i : ℝ) = ((t * G.denominator : ℕ) : ℝ) * (w.val i : ℝ) := by
  rw [(G.supply_integral _ w.property).choose_spec i]
  unfold supplyWidths
  push_cast
  field_simp [show (G.denominator : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr G.denominator_pos.ne']

/-- The finite supply list has the required integral norm bound at every multiple. -/
theorem supplyWidths_norm_le (t : ℕ) (w : G.supplies) :
    widthNorm q (fun i ↦ (G.supplyWidths t w i : ℝ)) ≤ (t * G.denominator : ℕ) * R := by
  simp_rw [cast_supplyWidths]
  rw [widthNorm_scale _ _ (by positivity)]
  exact mul_le_mul_of_nonneg_left (G.supply_norm _ w.property) (by positivity)

/-- At any positive multiple of the mesh denominator the integer widths retain
strict comparison. The supply index is chosen after the two distance patterns. -/
theorem integer_strict {t : ℕ} (ht : 0 < t) (z : G.demands) (d : D → ℝ) (e : S → ℝ)
    (he : ∀ i, 0 ≤ e i) (hE : 0 < distanceEnergy q e)
    (hcomp : distanceEnergy p d ≤ H * distanceEnergy q e) :
    ∃ w : G.supplies, wireValue (fun i ↦ (G.demandWidths t z i : ℝ)) d <
      wireValue (fun i ↦ (G.supplyWidths t w i : ℝ)) e := by
  obtain ⟨w, hw, hval⟩ := G.strict z z.property d e he hE hcomp
  refine ⟨⟨w, hw⟩, ?_⟩
  simp_rw [cast_demandWidths, cast_supplyWidths, wireValue_scale]
  exact mul_lt_mul_of_pos_left hval (Nat.cast_pos.mpr (Nat.mul_pos ht G.denominator_pos))

/-- Multiples of the common denominator can exceed any prescribed base size. -/
theorem exists_large_scale (b : ℕ) : ∃ t : ℕ, 0 < t ∧ b < t * G.denominator := by
  refine ⟨b + 1, Nat.succ_pos _, (Nat.lt_succ_self _).trans_le ?_⟩
  simpa using Nat.mul_le_mul_left (b + 1) G.denominator_pos

end StrictGrids

end MotifGrid

end VPVNP
end Computability
end OAI
