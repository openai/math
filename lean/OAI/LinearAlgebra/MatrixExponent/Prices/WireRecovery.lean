import OAI.LinearAlgebra.MatrixExponent.Sphere.Seam
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.LinearAlgebra.MatrixExponent.Prices.Space
import OAI.LinearAlgebra.MatrixExponent.Spectral.Placements
import OAI.LinearAlgebra.MatrixExponent.Spectral.Span
import OAI.LinearAlgebra.MatrixExponent.Sphere.TableMotion
import OAI.LinearAlgebra.MatrixExponent.Sphere.Width
import OAI.LinearAlgebra.MatrixExponent.Sphere.Coupled

section
/-!
# From one-site distance tests to saturation

A near-maximal level below energy `n` absorbs the logarithmic probe
error. Reusing the optimizing energies at scale `n+1` then gives a lower
bound on the increment of the unnormalized objective.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Sphere Real Filter Finset
open scoped Topology

private theorem probe_bound (U C η : ℝ) (hU : 0 ≤ U) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ w δ : ℝ, 0 ≤ w → w ≤ U → 0 ≤ δ →
      (∀ g ≤ n, δ * log (Fintype.card (Level 1 g)) ≤ w * entropy * sqrt g + C * log n) →
      δ ≤ w + η := by
  have hc := entropy_pos
  let b := entropy * η / 2
  have hb : 0 < b := by unfold b; positivity
  let a := b / (U + η)
  have ha : 0 < a := div_pos hb (by positivity)
  have hprod : a * (U + η) = b := div_mul_cancel₀ _ (by positivity)
  have ha' : a < entropy := by
    apply (div_lt_iff₀ (show 0 < U + η by positivity)).mpr
    unfold b
    nlinarith
  have hlev := (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (entropy_attained ha)
  have herr := ((isLittleO_log_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 2)).const_mul_left C).bound hb
  filter_upwards [hlev, tendsto_natCast_atTop_atTop.eventually herr, eventually_gt_atTop 0]
    with n hn hl hn₀
  intro w δ hw hw' hd h
  obtain ⟨g, hg, ht⟩ := hn
  simp only [Function.comp_apply, sq_sqrt (Nat.cast_nonneg n), Nat.cast_le] at hg ht
  have he : C * log n ≤ b * sqrt n := by
    apply le_trans (le_abs_self _)
    simpa only [norm_eq_abs, ← sqrt_eq_rpow, abs_of_nonneg (sqrt_nonneg _)] using hl
  have hk : δ * (entropy - a) ≤ w * entropy + b := by
    apply (mul_le_mul_iff_left₀ (show 0 < sqrt (n : ℝ) by positivity)).mp
    calc
      _ ≤ δ * log (Fintype.card (Level 1 g)) := by rw [mul_assoc]; gcongr
      _ ≤ w * entropy * sqrt g + C * log n := h g hg
      _ ≤ w * entropy * sqrt n + b * sqrt n := by gcongr
      _ = _ := (add_mul _ _ _).symm
  apply (mul_le_mul_iff_left₀ (sub_pos.mpr ha')).mp
  have := mul_le_mul_of_nonneg_left hw' ha.le
  unfold b at hprod hk
  linarith

variable {I : Type*} [Fintype I]

/-- The threshold depends only on a bound on the variance, the width cap
and the probe error, independently of the underlying spectral point. -/
theorem uniform_gap (D₀ U C : ℝ) (hU : 0 ≤ U) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (D : ℝ) (w : ℕ → I → ℝ) (B : ℕ → ℝ), D ≤ D₀ →
      (∀ m ≥ N, 0 ≤ B m) → (∀ m ≥ N, ∀ i, 0 ≤ w m i ∧ w m i ≤ U) →
      (∀ m ≥ N, ∃ δ : I → ℝ, (∀ i, 0 ≤ δ i) ∧ D ≤ ∑ i, δ i ^ 2 ∧
        ∀ i g, g ≤ m → δ i * log (Fintype.card (Level 1 g)) ≤
          w m i * entropy * sqrt g + C * log m) →
      (∀ m ≥ N, (∑ i, w m i ^ 2) * ((m : ℝ) / (m + 1)) ≤ 2 * (B (m + 1) - B m)) →
      D < 2 * (B n / n) + ε := by
  let L := (Fintype.card I : ℝ) * (2 * U + 1)
  have hL : 0 ≤ L := by unfold L; positivity
  let η := min 1 ((ε / 4) / (L + 1))
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hη' : η ≤ 1 := min_le_left _ _
  have hLη : L * η < ε / 4 := by
    have := (le_div_iff₀ (by positivity : 0 < L + 1)).mp (show η ≤ _ from min_le_right _ _)
    linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((eventually_ge_atTop N).and
    ((tendsto_natCast_atTop_atTop.eventually_ge_atTop (D₀ / (ε / 4))).and (probe_bound U C η hU hη)))
  filter_upwards [eventually_ge_atTop M, eventually_gt_atTop 0,
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (D₀ * M / (ε / 2))] with n hn hn₀ hlarge
  intro D w B hD₀ hB hw ht hstep
  have step (m : ℕ) (hm : M ≤ m) : D - ε / 2 ≤ 2 * (B (m + 1) - B m) := by
    obtain ⟨hN, hm', hb⟩ := hM m hm
    obtain ⟨δ, hδ, hD, hprobe⟩ := ht m hN
    have hi (i : I) : δ i ^ 2 ≤ w m i ^ 2 + (2 * U + 1) * η := by
      have hh := hb _ _ (hw m hN i).1 (hw m hN i).2 (hδ i) (hprobe i)
      have := pow_le_pow_left₀ (hδ i) hh 2
      nlinarith only [this, mul_le_mul_of_nonneg_right (hw m hN i).2 hη.le,
        mul_le_mul_of_nonneg_right hη' hη.le]
    have hh := hD.trans (sum_le_sum (fun i _ => hi i))
    rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_assoc] at hh
    have hb' : D - ε / 4 ≤ ∑ i, w m i ^ 2 := by unfold L at hLη; linarith
    refine le_trans ?_ (hstep m hN)
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity : 0 < ε / 4)] at hm'
    linarith only [mul_le_mul_of_nonneg_right hb' (Nat.cast_nonneg m), hε, hm', hD₀]
  have accum (k : ℕ) (hk : M ≤ k) : (D - ε / 2) * (k : ℝ) - D₀ * M ≤ 2 * B k := by
    induction k, hk using Nat.le_induction with
    | base =>
      have := mul_le_mul_of_nonneg_right (show D - ε / 2 ≤ D₀ by linarith) (Nat.cast_nonneg M)
      linarith only [this, hB M (hM M le_rfl).1]
    | succ k hk ih => push_cast; linarith only [ih, step k hk]
  rw [div_lt_iff₀ (half_pos hε)] at hlarge
  rw [← mul_div_assoc, ← sub_lt_iff_lt_add, lt_div_iff₀ (by positivity)]
  linarith only [hlarge, accum n hn]

theorem optimizer_limits {D U C : ℝ} (hU : 0 ≤ U) (r : I → ℝ)
    (w : ℕ → I → ℝ) (B : ℕ → ℝ)
    (hpos : ∀ᶠ n in atTop, 0 ≤ B n)
    (hw : ∀ᶠ n in atTop, ∀ i, 0 ≤ w n i ∧ w n i ≤ U)
    (ht : ∀ᶠ n : ℕ in atTop, ∃ δ : I → ℝ, (∀ i, 0 ≤ δ i) ∧ D ≤ ∑ i, δ i ^ 2 ∧
      ∀ i g, g ≤ n → δ i * log (Fintype.card (Level 1 g)) ≤
        w n i * entropy * sqrt g + C * log n)
    (hu : ∀ᶠ n : ℕ in atTop, 2 * (B n / n) + ∑ i, (w n i - r i) ^ 2 ≤ D)
    (hl : ∀ᶠ n : ℕ in atTop, (∑ i, w n i ^ 2) * ((n : ℝ) / (n + 1)) ≤ 2 * (B (n + 1) - B n)) :
    (∀ i, Tendsto (fun n => w n i) atTop (𝓝 (r i))) ∧
      Tendsto (fun n => B n / n) atTop (𝓝 (D / 2)) := by
  have hB : Tendsto (fun n => B n / n) atTop (𝓝 (D / 2)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hpos.and (hw.and (ht.and hl)))
      filter_upwards [uniform_gap (I := I) D U C hU N (D - 2 * a) (by linarith)] with n hn
      have := hn D w B le_rfl (fun m hm => (hN m hm).1) (fun m hm => (hN m hm).2.1)
        (fun m hm => (hN m hm).2.2.1) (fun m hm => (hN m hm).2.2.2)
      linarith
    · intro a ha
      filter_upwards [hu] with n hn
      have : 0 ≤ ∑ i, (w n i - r i) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
      linarith
  refine ⟨fun i => ?_, hB⟩
  have h₀ : Tendsto (fun n => D - 2 * (B n / n)) atTop (𝓝 0) := by
    convert (hB.const_mul 2).const_sub D using 1
    congr 1; ring
  have hsq : Tendsto (fun n => (w n i - r i) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) ?_ h₀
    filter_upwards [hu] with n hn
    have := single_le_sum (fun j (_ : j ∈ univ) => sq_nonneg (w n j - r j)) (mem_univ i)
    linarith
  apply tendsto_sub_nhds_zero_iff.mp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_eq_abs, sqrt_sq_eq_abs, sqrt_zero] using hsq.sqrt

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# The cost of a separated coefficient array and a linear combination

Use natural logarithms for leg dimensions. Wire prices on binary legs
are distances, so the corresponding array prices are multiplied by
the natural logarithm of two.
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral
open scoped Classical

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A]
variable {Y : Type*} [MetricSpace Y] {x : A → Y} {P : Tensor F A → ℝ}

def ExtendsAt (P : Tensor F A → ℝ) (x : A → Y) : Prop :=
  ∀ D : ℝ, 0 < D → (∀ a b, dist (x a) (x b) ≤ D) → Realized x P D

theorem ExtendsAt.prices (h : ExtendsAt P x) {U : Type} [Fintype U]
    [DecidableEq U] [Nonempty U] (z : U → Y) :
    ∃ d : ℝ, 0 ≤ d ∧ ∃ f : Tensor F (A ⊕ U) →+* ℝ, Monotone f ∧
      (∀ T, P T * Real.log 2 = d * Real.log (f (Tensor.pad U T))) ∧
      ∀ i j, d * Tensor.dist f i j = dist (Sum.elim x z i) (Sum.elim x z j) := by
  let r (i : (A ⊕ U) × (A ⊕ U)) := dist (Sum.elim x z i.1) (Sum.elim x z i.2)
  obtain ⟨B, hB⟩ := (Set.finite_range r).bddAbove
  let D := max B 1
  have hd : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hb (i j : A ⊕ U) : dist (Sum.elim x z i) (Sum.elim x z j) ≤ D :=
    (hB ⟨(i, j), rfl⟩).trans (le_max_left _ _)
  have hh := h D hd (fun i j => hb (.inl i) (.inl j))
  obtain ⟨_, ⟨d, h₀, f, hf, rfl⟩, he, he'⟩ := hh.2 U z
    (fun i j => (hb i j).trans (by linarith))
  refine ⟨d, h₀.1, f, hf, ?_, he'⟩
  intro T
  rw [← he, Tensor.values, mul_assoc, div_mul_cancel₀ _ (Real.log_pos (by norm_num)).ne']

variable (X : A → Type) [∀ i, Fintype (X i)]

def tablePrice (P : Tensor F A → ℝ) (T : (∀ i, X i) → F) : ℝ :=
  P (Tensor.ofRaw (Raw.ofTable X T)) * Real.log 2

/-- Send the two groups from distinct sites with an intermediate leg
whose dimension is the number of separated summands. -/
theorem ExtendsAt.cut (h : ExtendsAt P x) (T : (∀ i, X i) → F) (B : Finset A)
    {J : Type} [Fintype J] (L R : J → (∀ i, X i) → F)
    (hs : ∀ v, T v = ∑ j, L j v * R j v)
    (hl : ∀ j v w, (∀ i ∈ B, v i = w i) → L j v = L j w)
    (hr : ∀ j v w, (∀ i ∉ B, v i = w i) → R j v = R j w) (m o : Y) :
    tablePrice X P T ≤ dist o m * Real.log (Fintype.card J) +
      ∑ i, dist (if i ∈ B then m else o) (x i) * Real.log (Fintype.card (X i)) := by
  let z (b : Bool) := if b then m else o
  obtain ⟨d, hd, f, hf, he, hw⟩ := h.prices z
  let U := Raw.ofTable X T
  unfold tablePrice
  rw [he]
  by_cases hU : Tensor.ofRaw U = 0
  · rw [show Tensor.ofRaw (Raw.ofTable X T) = 0 from hU, (Tensor.padding Bool).zero,
      map_zero, Real.log_zero, mul_zero]
    positivity
  have hJ : 0 < Fintype.card J := by
    by_contra! hj
    have : IsEmpty J := Fintype.card_eq_zero_iff.mp (by omega)
    apply hU
    refine (Tensor.ofRaw_eq_zero _).mpr ?_
    change ∀ v : (∀ i, X i), (Raw.ofTable X T).coeff v = 0
    simp [hs]
  let a : A ⊕ Bool := .inr true
  let b : A ⊕ Bool := .inr false
  let p (i : A) := if i ∈ B then a else b
  have hm : Tensor.place p (Tensor.ofRaw U) ≤ Tensor.wire F a b (Fintype.card J) :=
    Tensor.separated_le X T (· ∈ B) L R hs hl hr a b
  have hcut := Real.log_le_log (Tensor.price_place_pos f hf p hU) (hf hm)
  rw [Tensor.price_wire f hf _ _ hJ, Real.log_rpow (Nat.cast_pos.mpr hJ)] at hcut
  have hc := mul_le_mul_of_nonneg_left hcut hd
  rw [← mul_assoc, hw, show Sum.elim x z a = m from rfl, show Sum.elim x z b = o from rfl,
    dist_comm m o] at hc
  have ht := (abs_sub_le_iff.mp (Tensor.price_transport f hf U hU p Sum.inl)).2
  rw [Tensor.place_inl] at ht
  have hh := mul_le_mul_of_nonneg_left ht hd
  simp only [mul_sub, Finset.mul_sum, ← mul_assoc, hw, Sum.elim_inl] at hh
  have hp (i : A) : Sum.elim x z (p i) = if i ∈ B then m else o := by
    by_cases hi : i ∈ B <;> simp [p, hi, z, a, b]
  simp only [hp] at hh
  change _ ≤ ∑ i, dist (if i ∈ B then m else o) (x i) * Real.log (Fintype.card (X i)) at hh
  change d * Real.log (f (Tensor.pad Bool (Tensor.ofRaw U))) ≤ _
  linarith only [hc, hh]

/-- In a finite span one summand has cost within the logarithm of the
number of summands, times a fixed scale, of the total cost. -/
theorem ExtendsAt.span (h : ExtendsAt P x) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ (X : A → Type) [∀ i, Fintype (X i)]
      (T : (∀ i, X i) → F) (s : Finset ((∀ i, X i) → F)),
      0 < tablePrice X P T → T ∈ Submodule.span F (s : Set _) →
      ∃ v ∈ s, tablePrice X P T ≤ tablePrice X P v + d * Real.log s.card := by
  obtain ⟨d, hd, f, hf, he, _⟩ := h.prices x
  refine ⟨d, hd, fun X _ T s hp ht => ?_⟩
  let V (v : (∀ i, X i) → F) := Tensor.ofRaw (Raw.ofTable X v)
  let val (v : (∀ i, X i) → F) := f (Tensor.pad A (V v))
  have hprice (v) : tablePrice X P v = d * Real.log (val v) := he _
  have hpos : 0 < val T := by
    have hn : 0 ≤ val T := by simpa using hf (Tensor.zero_le (Tensor.pad A (V T)))
    refine lt_of_le_of_ne hn (fun hz => ?_)
    simp [hprice, ← hz] at hp
  obtain ⟨c, _, hc⟩ := Submodule.mem_span_finset.mp ht
  have hrel : V T ≤ ∑ v ∈ s, V v := by
    rw [← Finset.sum_coe_sort]
    apply Tensor.span_le X T Subtype.val (fun v => c v.val)
    intro z
    have hh := congrFun hc z
    rw [Finset.sum_coe_sort s (fun v => c v * v z)]
    simpa [Finset.sum_apply] using hh.symm
  have subadd (u : Finset ((∀ i, X i) → F)) :
      f (Tensor.pad A (∑ v ∈ u, V v)) ≤ ∑ v ∈ u, val v := by
    induction u using Finset.induction with
    | empty => simp [(Tensor.padding A).zero]
    | @insert v u hv ih =>
      rw [Finset.sum_insert hv, Finset.sum_insert hv]
      have ha := hf ((Tensor.padding A).add_le (V v) (∑ w ∈ u, V w))
      rw [map_add] at ha
      exact ha.trans (add_le_add_right ih _)
  have hsum : val T ≤ ∑ v ∈ s, val v :=
    (hf (((Tensor.padding A).le_iff _ _).mpr hrel)).trans (subadd s)
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun he => by
    rw [he, Finset.sum_empty] at hsum
    exact hpos.not_ge hsum
  obtain ⟨v, hv, hm⟩ := Finset.exists_max_image s val hne
  have hh : val T ≤ s.card * val v := calc
    _ ≤ ∑ u ∈ s, val u := hsum
    _ ≤ ∑ _u ∈ s, val v := Finset.sum_le_sum hm
    _ = _ := by simp
  have hsc : 0 < (s.card : ℝ) := Nat.cast_pos.mpr hne.card_pos
  have hv' : 0 < val v := (mul_pos_iff_of_pos_left hsc).mp (hpos.trans_le hh)
  have hl := Real.log_le_log hpos hh
  rw [Real.log_mul hsc.ne' hv'.ne'] at hl
  refine ⟨v, hv, ?_⟩
  rw [hprice, hprice, ← mul_add, add_comm]
  exact mul_le_mul_of_nonneg_left hl hd

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! The unit-mass sphere price profile in doubled energy units. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Sphere Spectral Filter
open scoped Topology

def width (e : ℕ) := Sphere.entropy * Real.sqrt e

theorem width_nonneg (e : ℕ) : 0 ≤ width e :=
  mul_nonneg entropy_pos.le (Real.sqrt_nonneg _)

theorem width_sq (e : ℕ) : width e ^ 2 = entropy ^ 2 * e := by
  rw [width, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A]

def sphereForm (z : A → F) (e : A → ℕ) (x : States 1 e) : F :=
  wick (fun i j => fieldKernel (z i.1, i.2) (z j.1, j.2)) (inputs x)

def sphereTensor (z : A → F) (e : A → ℕ) : Tensor F A :=
  Tensor.ofRaw (Raw.ofTable (fun i => Level 1 (e i)) (sphereForm z e))

def spherePrice (P : Tensor F A → ℝ) (z : A → F) (e : A → ℕ) : ℝ :=
  tablePrice (fun i => Level 1 (e i)) P (sphereForm z e)

/-- Unit-mass saturation at the specified point placement and sphere
positions, with a price compatible with all auxiliary placements. -/
def Saturation (F : Type) [Field F] (Y : Type*) [MetricSpace Y] : Prop :=
  ∀ {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] (x : A → Y) (o : Y), Bary x o →
    ∀ z : A → F, Function.Injective z →
    ∃ P : Tensor F A → ℝ, ExtendsAt P x ∧ ∃ e : ℕ → A → ℕ,
      (∀ i, Tendsto (fun n => width (e n i) / (n : ℝ)) atTop (𝓝 (dist o (x i)))) ∧
      Tendsto (fun n => spherePrice P z (e n) / (n : ℝ)) atTop (𝓝 (∑ i, dist o (x i) ^ 2))

variable {Y : Type*} [MetricSpace Y] {x : A → Y} {P : Tensor F A → ℝ}

theorem ExtendsAt.spherePrice_nonneg (h : ExtendsAt P x) (z : A → F) (e : A → ℕ) :
    0 ≤ spherePrice P z e := by
  obtain ⟨d, hd, f, hf, he, _⟩ := h.prices x
  unfold spherePrice tablePrice
  rw [he]
  apply mul_nonneg hd
  generalize Tensor.pad (K := F) (S := A) A _ = T
  by_cases hT : T = 0
  · simp [hT]
  exact Real.log_nonneg (Tensor.value_one_le hf hT)

theorem ExtendsAt.spherePrice_le (h : ExtendsAt P x) (z : A → F) (e : A → ℕ) (o : Y) :
    spherePrice P z e ≤ ∑ i, dist o (x i) * width (e i) := by
  have hc := h.cut (fun i => Level 1 (e i)) (sphereForm z e) ∅
    (fun (_ : Unit) _ => 1) (fun _ v => sphereForm z e v)
    (by simp) (by simp) (fun _ v w he => congrArg _ (funext (fun i => he i (by simp)))) o o
  simp only [dist_self, zero_mul, zero_add, ite_self] at hc
  exact hc.trans (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (entropy_bound _) dist_nonneg))

theorem ExtendsAt.spherePrice_zero (h : ExtendsAt P x) {z : A → F} {e : A → ℕ}
    (he : sphereForm z e = 0) : spherePrice P z e = 0 := by
  have ht : Tensor.ofRaw (Raw.ofTable (fun i => Level 1 (e i)) (sphereForm z e)) = 0 := by
    refine (Tensor.ofRaw_eq_zero _).mpr ?_
    change ∀ v : States 1 e, (Raw.ofTable (fun i => Level 1 (e i)) (sphereForm z e)).coeff v = 0
    simp [he]
  obtain ⟨d, hd, f, hf, hp, _⟩ := h.prices x
  rw [spherePrice, tablePrice, ht, hp, (Tensor.padding A).zero, map_zero, Real.log_zero, mul_zero]

omit [DecidableEq A] [Nonempty A] in
theorem sphereForm_vacuum (z : A → F) : sphereForm z (fun _ => 0) ≠ 0 := by
  let w : States 1 (fun _ : A => 0) := fun _ => ⟨⟨[], by simp⟩, rfl⟩
  intro h
  have he := congrFun h w
  have hw : marksAt w = fun _ => [] := rfl
  have hf (l : List A) : l.flatMap (marksAt w) = [] := by
    induction l with
    | nil => rfl
    | cons j l ih => rw [List.flatMap_cons, ih, hw]; rfl
  simp [sphereForm, inputs, hf] at he

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! # Quadratic objective and one-site probes for a maximizing sphere -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Sphere Spectral Filter

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A]

def objective (P : Tensor F A → ℝ) (z : A → F) (n : ℕ) (e : A → ℕ) : ℝ :=
  spherePrice P z e - (∑ i, width (e i) ^ 2) / (2 * n)

/-- The finite optimizer test uses only a single extra site and probes of
doubled energy at most `n`. -/
def Controlled (F : Type) [Field F] (Y : Type*) [MetricSpace Y] : Prop :=
  ∀ {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] (x : A → Y) (o : Y), Bary x o →
    ∀ z : A → F, Function.Injective z →
    ∃ P : Tensor F A → ℝ, ExtendsAt P x ∧ ∀ R : ℝ, 0 < R → ∃ C : ℝ,
      ∀ᶠ n : ℕ in atTop, ∀ e : A → ℕ, (∀ h, objective P z n h ≤ objective P z n e) →
        (∀ i, (e i : ℝ) ≤ R * (n : ℝ) ^ 2) → sphereForm z e ≠ 0 →
        ∃ δ : A → ℝ, (∀ i, 0 ≤ δ i) ∧ (∑ i, dist o (x i) ^ 2) ≤ ∑ i, δ i ^ 2 ∧
          ∀ i g, g ≤ n → δ i * Real.log (Fintype.card (Level 1 g)) ≤
            width (e i) * width g / n + C * Real.log n

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! The product test for sphere forms with one shared moving insertion. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral

def BoundedForms (F : Type) [Field F] : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] (f : Tensor F A →+* ℝ),
    Monotone f → ∀ z : A → F, Function.Injective z →
    ∀ (B : ℝ) (t : A ⊕ Unit → ℝ), (∀ i, 0 ≤ t i ∧ t i ≤ t (.inr ())) →
    (∀ e, f (sphereTensor z e) ≤ Real.exp (B + ∑ i, t (.inl i) * (e i : ℝ))) →
    ∀ s : F, s ∉ Set.range z → ∀ (M : ℕ) (w : List (A ⊕ Unit → ℕ)),
    (∀ e ∈ w, ∀ i, e i ≤ M) → ∀ T, Tensor.pad Unit T ≤
      (w.map (sphereTensor (Sum.elim z (fun _ => s)))).prod →
    f T ≤ (w.map (fun e => ((M : ℝ) + 2) ^ (Fintype.card A + 8) *
      Real.exp (B + ∑ i, t i * (e i : ℝ)))).prod

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! One-site extension conditions for the sphere price argument. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral

def VarianceTest (F : Type) [Field F] (Y : Type*) [MetricSpace Y] : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] [Nontrivial A] (x : A → Y) (o : Y),
    Bary x o → ∃ d : ℝ, 0 ≤ d ∧ ∃ f : Tensor F A →+* ℝ, Monotone f ∧
      ExtendsAt (Tensor.values d f) x ∧
      ∀ g : Tensor F (A ⊕ Unit) →+* ℝ, Monotone g →
        (∀ T, g (Tensor.pad Unit T) = f T) →
        (∑ i, dist o (x i) ^ 2) ≤ ∑ i, (d * Tensor.dist g (.inl i) (.inr ())) ^ 2

def BoundedExtension (F : Type) [Field F] : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] (f : Tensor F A →+* ℝ),
    Monotone f → ∀ z : A → F, Function.Injective z →
    ∀ (B t : ℝ), 0 ≤ t →
    (∀ e, f (sphereTensor z e) ≤ Real.exp (B + ∑ i, t * (e i : ℝ))) →
    ∀ M : ℕ, ∃ g : Tensor F (A ⊕ Unit) →+* ℝ, Monotone g ∧
      (∀ T, g (Tensor.pad Unit T) = f T) ∧
      ∀ (s : F), s ∉ Set.range z → ∀ e : A ⊕ Unit → ℕ, (∀ i, e i ≤ M) →
        g (sphereTensor (Sum.elim z (fun _ => s)) e) ≤
          ((M : ℝ) + 2) ^ (Fintype.card A + 8) * Real.exp (B + ∑ i, t * (e i : ℝ))

def WireProbe (F : Type) [Field F] : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] (z : A → F), Function.Injective z →
    ∀ (e : A → ℕ) (i : A) (q : ℕ),
      let H := ⌊Sphere.width q (e i)⌋₊
      ∃ T : Finset F, (∀ s ∈ T, s ∉ Set.range z) ∧
        T.card ≤ 1 + Fintype.card A * ((∑ j, e j) + H + q) ∧
        Tensor.pad Unit (sphereTensor z e) * Tensor.wire F (.inl i) (.inr ())
          (Fintype.card (Sphere.Level 1 q)) ≤
          ∑ h ∈ Finset.range (H + 1), ∑ s ∈ T,
            sphereTensor (Sum.elim z (fun _ => s)) (Sum.elim (Function.update e i h) (fun _ => q))

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Coordinates for a moving sphere insertion

Site permutations contribute signs that are common to all basis
indices at the specified energies and all positions of the moving site.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Insertion

open Finset Sphere Sphere.Motion
open scoped Classical

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A]

def marks (z : A → F) : Finset F := univ.image z
def mark (z : A → F) (i : A) : ↥(marks z) := ⟨z i, mem_image_of_mem _ (mem_univ i)⟩

abbrev energy (e : A → ℕ) (g : ℕ) : A ⊕ Unit → ℕ := Sum.elim e (fun _ => g)

def add {e : A → ℕ} (x : States 1 e) {g : ℕ} (w : Level 1 g) : States 1 (energy e g)
  | .inl i => x i
  | .inr _ => w

def changeAt {e : A → ℕ} (i : A) (x : States 1 e) {h : ℕ} (w : Level 1 h) :
    States 1 (Function.update e i h) := fun j =>
  ⟨Function.update (fun l => (x l).val) i w.val j, by
    by_cases hj : j = i
    · subst j
      simpa using w.2
    · simpa [hj] using (x j).2⟩

omit [Fintype A] in
@[simp] theorem changeAt_val {e : A → ℕ} (i : A) (x : States 1 e) {h : ℕ} (w : Level 1 h) (j : A) :
    (changeAt i x w j).val = if j = i then w.val else (x j).val := by
  simp [changeAt, Function.update_apply]

def rest (z : A → F) (i : A) {e : A → ℕ} (x : States 1 e) : List (↥(marks z) × Mode 1) :=
  (univ.erase i).toList.flatMap (fun j => (x j).val.val.map (mark z j, ·))

omit [Field F] in
theorem rest_avoids (z : A → F) (hz : Function.Injective z) (i : A) {e : A → ℕ} (x : States 1 e) :
    ∀ y ∈ rest z i x, y.1 ≠ mark z i := by
  intro y hy eq
  obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hy
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm
  exact (mem_erase.mp (mem_toList.mp hj)).1 (hz (congrArg Subtype.val eq))

omit [Field F] in
theorem weight_rest (z : A → F) (i : A) {e : A → ℕ} (x : States 1 e) :
    weight (rest z i x) = ∑ j ∈ univ.erase i, e j := by
  have h := weight_list x (univ.erase i).toList
  rw [← List.sum_toFinset e (nodup_toList _), toList_toFinset] at h
  rw [← h]
  simp [weight, rest, List.map_flatMap, marksAt, Function.comp_def]

omit [Field F] in
@[simp] theorem rest_changeAt (z : A → F) (i : A) {e : A → ℕ}
    (x : States 1 e) {h : ℕ} (w : Level 1 h) : rest z i (changeAt i x w) = rest z i x := by
  apply List.flatMap_congr
  intro j hj
  rw [changeAt_val, ite_eq_right (mem_erase.mp (mem_toList.mp hj)).1]

omit [DecidableEq A] in
private theorem order (e : A → ℕ) (l : List A) (hl : univ.toList.Perm l) :
    ∃ c : F, c ≠ 0 ∧ ∀ (z : A → F) (x : States 1 e),
      sphereForm z e x = c * wick fieldKernel
        (l.flatMap fun j => (x j).val.val.map (z j, ·)) := by
  obtain ⟨n, hn⟩ := wick_perm_sites (R := F) (r := 1) e hl
  refine ⟨(-1) ^ n, by simp, fun z x => ?_⟩
  let u (i : A × Mode 1) := (z i.1, i.2)
  have h := hn (fun i j => fieldKernel (u i) (u j))
    (fun i j => fieldKernel_skew _ _) x []
  simp only [List.nil_append] at h
  change sphereForm z e x = _ at h
  rw [h, ← wick_map fieldKernel u]
  simp [u, List.map_flatMap, marksAt, Function.comp_def]

theorem order_base (z : A → F) (i : A) (e : A → ℕ) :
    ∃ c : F, c ≠ 0 ∧ ∀ x : States 1 e, sphereForm z e x = c *
      wick fieldKernel ((x i).val.val.map (z i, ·) ++ spectators (rest z i x)) := by
  have hp : univ.toList.Perm (i :: (univ.erase i).toList) := by
    apply (List.perm_ext_iff_of_nodup (nodup_toList _) (by simp [nodup_toList])).mpr
    simp [eq_or_ne]
  obtain ⟨c, hc, h⟩ := order (F := F) e _ hp
  refine ⟨c, hc, fun x => ?_⟩
  rw [h]
  simp [spectators, rest, mark, List.map_flatMap, Function.comp_def]

private theorem added_perm (i : A) :
    (univ : Finset (A ⊕ Unit)).toList.Perm (.inl i :: .inr () :: (univ.erase i).toList.map Sum.inl) := by
  let l : List (A ⊕ Unit) := .inl i :: .inr () :: (univ.erase i).toList.map Sum.inl
  have hp : univ.toList.Perm l := by
    have hn : l.Nodup := by
      simp [l, nodup_toList, List.nodup_map_iff Sum.inl_injective]
    apply (List.perm_ext_iff_of_nodup (nodup_toList _) hn).mpr
    rintro (j | ⟨⟩) <;> simp [l, eq_or_ne]
  exact hp

theorem order_added (z : A → F) (i : A) (e : A → ℕ) (g : ℕ) :
    ∃ c : F, c ≠ 0 ∧ ∀ (s : F) (x : States 1 e) (w : Level 1 g),
      sphereForm (Sum.elim z (fun _ => s)) (energy e g) (add x w) = c *
        wick fieldKernel ((triple (mark z i) (x i).val.val w.val.val (rest z i x)).map (atPoint s)) := by
  let l : List (A ⊕ Unit) := .inl i :: .inr () :: (univ.erase i).toList.map Sum.inl
  have hp : univ.toList.Perm l := added_perm i
  obtain ⟨c, hc, h⟩ := order (F := F) (energy e g) _ hp
  refine ⟨c, hc, fun s x w => ?_⟩
  rw [h]
  simp [triple, rest, mark, List.map_flatMap, Function.comp_def, l, List.flatMap_map, add, atPoint]

/-- A common numerator in any of the pole orderings. -/
theorem order_polynomial (z : A → F) (e : A ⊕ Unit → ℕ) :
    ∃ P : States 1 e → Polynomial F, ∀ i : A, ∃ t : F, t ≠ 0 ∧
      ∀ x : States 1 e, P x = Polynomial.C t * numerator (marks z)
        (triple (mark z i) (x (.inl i)).val.val (x (.inr ())).val.val
          (rest z i (fun j => x (.inl j)))) := by
  let u (x : (A ⊕ Unit) × Mode 1) : Option ↥(marks z) × Mode 1 :=
    (Sum.elim (fun i => some (mark z i)) (fun _ => none) x.1, x.2)
  let k := polynomialKernel (r := 1) (trajectories (marks z)) (Polynomial.X : Polynomial F) 1
  refine ⟨fun x => wick (fun i j => k (u i) (u j)) (inputs x), fun i => ?_⟩
  let l : List (A ⊕ Unit) := .inl i :: .inr () :: (univ.erase i).toList.map Sum.inl
  have hp : univ.toList.Perm l := added_perm i
  obtain ⟨n, hn⟩ := wick_perm_sites (R := Polynomial F) (r := 1) e hp
  refine ⟨(-1) ^ n, by simp, fun x => ?_⟩
  have h := hn (fun i j => k (u i) (u j)) (fun i j => polynomial_skew _ (u i) (u j)) x []
  simp only [List.nil_append] at h
  change wick (fun i j => k (u i) (u j)) (univ.toList.flatMap (marksAt x)) = _
  rw [h, ← wick_map k u, map_pow, map_neg, map_one]
  simp [numerator, correlatorPoly, k, triple, rest, marksAt, u, List.map_flatMap,
    Function.comp_def, l, List.flatMap_map]

end OAI.LinearAlgebra.MatrixExponent.Routing.Insertion
end

/-!
# Recovering the entries of a wire at one site

All coefficients of the interpolation and the matrix units are
independent of basis indices held at other sites.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Insertion

open Finset Sphere Sphere.Motion
open scoped Classical

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A]

private theorem units {q e : ℕ} (a : Level 1 q) (b : Level 1 e) :
    ∃ v : Wedge 1 → F, ∀ (x : Level 1 q) (y : Level 1 e),
      (∑ h ∈ range (⌊Sphere.width q e⌋₊ + 1), ∑ t : Level 1 h,
        v t.val * fusion F t.val.val x.val.val y.val.val) =
          if a = x ∧ b = y then 1 else 0 := by
  obtain ⟨v, hv, he⟩ := fusion_width F a.val b.val
  have hs (t : Wedge 1) (ht : t ∈ v.support) :
      Sphere.energy t.val ∈ range (⌊Sphere.width q e⌋₊ + 1) := by
    refine mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ?_))
    simpa only [a.2, b.2] using hv t ht
  refine ⟨v, fun x y => ?_⟩
  have hh := he x.val y.val (x.2.trans a.2.symm) (y.2.trans b.2.symm)
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, ← Subtype.ext_iff] at hh
  rw [← hh, ← sum_fiberwise_of_maps_to hs]
  refine sum_congr rfl fun h _ => ?_
  symm
  refine sum_bij_ne_zero (fun t ht _ => ⟨t, (mem_filter.mp ht).2⟩)
    (fun _ _ _ => mem_univ _) (fun _ _ _ _ _ _ he => congrArg Subtype.val he)
    ?_ (fun _ _ _ => rfl)
  intro t _ ht
  have hv' : t.val ∈ v.support := Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul ht)
  exact ⟨t.val, mem_filter.mpr ⟨hv', t.2⟩, ht, rfl⟩

variable (z : A → F) (i : A) (e : A → ℕ) (q : ℕ)

private theorem coefficient (hz : Function.Injective z) (T : Finset F) (hd : Disjoint T (marks z))
    (h : ℕ) (hT : (marks z).card * ((h + q + ∑ j ∈ univ.erase i, e j) / 2) < T.card) :
    ∃ f : T → F, ∀ (x : States 1 e) (a : Level 1 h) (w : Level 1 q),
      (∑ b : Level 1 (e i), fusion F a.val.val w.val.val b.val.val *
        stationary (mark z i) b.val (rest z i x)) =
      ∑ s : T, f s * sphereForm (Sum.elim z (fun _ => s.val))
        (energy (Function.update e i h) q) (add (changeAt i x a) w) := by
  obtain ⟨f, hf⟩ := recover_level (r := 1) (mark z i) T hd h q (e i) _ hT
  obtain ⟨c, hc, hc'⟩ := order_added z i (Function.update e i h) q
  refine ⟨fun s => f s / c, fun x a w => ?_⟩
  rw [hf a w.val _ w.2 (rest_avoids z hz i x) (weight_rest _ _ _)]
  refine sum_congr rfl fun s _ => ?_
  rw [hc', changeAt_val, ite_eq_left rfl, rest_changeAt, ← mul_assoc, div_mul_cancel₀ _ hc]
  rfl

private theorem eval_units (q e : ℕ) (w : Level 1 q) (b : Level 1 e)
    (f : Level 1 e → F) (v : Wedge 1 → F)
    (hv : ∀ (t : Level 1 q) (y : Level 1 e),
      (∑ h ∈ range (⌊Sphere.width q e⌋₊ + 1), ∑ a : Level 1 h,
        v a.val * fusion F a.val.val t.val.val y.val.val) =
          if w = t ∧ b = y then 1 else 0) (t : Level 1 q) :
    (∑ h ∈ range (⌊Sphere.width q e⌋₊ + 1), ∑ a : Level 1 h, v a.val *
      ∑ y, fusion F a.val.val t.val.val y.val.val * f y) =
        if w = t then f b else 0 := by
  have hh (h : ℕ) :
      (∑ a : Level 1 h, v a.val * ∑ y, fusion F a.val.val t.val.val y.val.val * f y) =
      ∑ y, (∑ a : Level 1 h, v a.val * fusion F a.val.val t.val.val y.val.val) * f y := by
    simp only [mul_sum, sum_mul, mul_assoc]
    rw [sum_comm]
  simp_rw [hh]
  rw [sum_comm]
  simp_rw [← sum_mul, hv]
  by_cases he : w = t <;> simp [he]

theorem recover_wire (hz : Function.Injective z) (T : Finset F) (hd : Disjoint T (marks z))
    (hT : Fintype.card A * ((∑ j, e j) + ⌊Sphere.width q (e i)⌋₊ + q) < T.card) :
    ∃ k : ∀ h : ℕ, T → Level 1 h → Level 1 (e i) → Level 1 q → F,
      ∀ (x : States 1 e) (w t : Level 1 q),
        (if w = t then sphereForm z e x else 0) =
        ∑ h ∈ range (⌊Sphere.width q (e i)⌋₊ + 1), ∑ s : T, ∑ a : Level 1 h,
          k h s a (x i) w * sphereForm (Sum.elim z (fun _ => s.val))
            (energy (Function.update e i h) q) (add (changeAt i x a) t) := by
  let H := ⌊Sphere.width q (e i)⌋₊
  have he (h : ℕ) (hh : h ∈ range (H + 1)) :
      (marks z).card * ((h + q+∑ j ∈ univ.erase i, e j) / 2) < T.card := by
    refine lt_of_le_of_lt (Nat.mul_le_mul card_image_le ?_) hT
    have := mem_range.mp hh
    have := sum_erase_add univ e (mem_univ i)
    omega
  choose! f hf using fun h hh => coefficient z i e q hz T hd h (he h hh)
  choose v hv using fun (w : Level 1 q) (b : Level 1 (e i)) => units (F := F) w b
  obtain ⟨c, _, hc⟩ := order_base z i e
  refine ⟨fun h s a b w => c * v w b a.val * f h s, fun x w t => ?_⟩
  let g (y : Level 1 (e i)) := stationary (mark z i) y.val (rest z i x)
  rw [show sphereForm z e x = c * g (x i) from hc x, show (if w = t then c * g (x i) else 0) = c * (if w = t then g (x i) else 0) by simp]
  rw [← eval_units _ _ w (x i) g (v w (x i)) (hv w (x i)) t, mul_sum]
  refine sum_congr rfl fun h hh => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  dsimp only [g]
  rw [hf h hh x a t, mul_sum, mul_sum]
  exact sum_congr rfl (fun _ _ => by ring)

end OAI.LinearAlgebra.MatrixExponent.Routing.Insertion
end

/-! Recovery of one full wire by a sum of local tensor restrictions. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral Sphere Finset
open scoped Classical

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A]

/-- A sum whose evaluation varies only at site `i` is one local map. -/
private theorem mix_at {J : Type} [Fintype J] (U V : Raw F A) (i : A)
    (k : J → V.leg i → F) (f : J → ∀ a, V.leg a → U.leg a)
    (h : ∀ u v a, a ≠ i → f u a = f v a) (scale : ∀ a, V.leg a → F) :
    ∃ M : Raw.Local U V, ∀ x, U.applyLocal M x =
      (∏ a, scale a (x a)) * ∑ j, k j (x i) * U.coeff (fun a => f j a (x a)) := by
  let base : Raw.Local U V := if hJ : Nonempty J then
    fun a x z => if z = f hJ.some a x then 1 else 0 else fun _ _ _ => 0
  let N := Function.update base i (fun x z => ∑ j, if z = f j i x then k j x else 0)
  refine ⟨fun a x z => scale a x * N a x z, fun x => ?_⟩
  have hv (t : U.term) :
      ∑ z, N i (x i) z * U.factor t i z = ∑ j, k j (x i) * U.factor t i (f j i (x i)) := by
    simp only [N, Function.update_self, sum_mul]
    rw [sum_comm]
    simp [ite_mul]
  have hu (t : U.term) (j : J) (a : A) (ha : a ∈ univ.erase i) :
      ∑ z, N a (x a) z * U.factor t a z = U.factor t a (f j a (x a)) := by
    have hai := (mem_erase.mp ha).1
    have hJ : Nonempty J := ⟨j⟩
    simp [N, hai, base, hJ, h hJ.some j a hai, ite_mul]
  have step (t : U.term) :
      (∏ a, ∑ z, N a (x a) z * U.factor t a z) =
      ∑ j, k j (x i) * ∏ a, U.factor t a (f j a (x a)) := by
    rw [← mul_prod_erase _ _ (mem_univ i), hv, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [prod_congr rfl (hu t j), mul_assoc, mul_prod_erase _ (fun a => U.factor t a (f j a (x a))) (mem_univ i)]
  simp only [Raw.applyLocal, mul_assoc, ← mul_sum, prod_mul_distrib, step]
  rw [sum_comm]
  simp only [Raw.coeff, ← mul_sum]

private theorem wire_coeff (i : A) (n : ℕ) [NeZero n] (x : A ⊕ Unit → Fin n) :
    (Raw.wire F (.inl i) (.inr ()) n).coeff x =
      (∏ a, if a ∈ ({.inl i, .inr ()} : Finset (A ⊕ Unit)) ∨ x a = 0 then (1 : F) else 0) *
        (if x (.inl i) = x (.inr ()) then 1 else 0) := by
  let U : Finset (A ⊕ Unit) := {.inl i, .inr ()}
  change (∑ j : Fin n, ∏ a, if x a = Raw.port U a j then (1 : F) else 0) = _
  rw [Fintype.sum_eq_single (x (.inr ()))]
  · have eqn (a : A ⊕ Unit) :
        (if x a = Raw.port U a (x (.inr ())) then (1 : F) else 0) =
          (if a ∈ U ∨ x a = 0 then 1 else 0) *
          (if a = .inl i then if x (.inl i) = x (.inr ()) then 1 else 0 else 1) := by
      rcases a with j | ⟨⟩
      · by_cases h : j = i <;> simp [Raw.port, U, h]
      · simp [Raw.port, U]
    simp only [eqn, prod_mul_distrib]
    simp [U]
  · intro j hj
    exact prod_eq_zero (mem_univ (.inr ())) (by simp [Raw.port, U, Ne.symm hj])

open Insertion

variable [Nonempty A]

private def selectWord {e : A → ℕ} (i j : A) {h : ℕ} (v : Level 1 h) (w : Level 1 (e j)) :
    Level 1 (Function.update e i h j) :=
  ⟨if j = i then v.val else w.val, by
    by_cases hj : j = i
    · simpa [hj] using v.2
    · simpa [hj] using w.2⟩

private theorem probe (z : A → F) (hz : Function.Injective z) (e : A → ℕ) (i : A) (q : ℕ)
    (T : Finset F) (hd : Disjoint T (Insertion.marks z))
    (hT : Fintype.card A * ((∑ j, e j) + ⌊Sphere.width q (e i)⌋₊ + q) < T.card) :
    Tensor.pad Unit (sphereTensor z e) * Tensor.wire F (.inl i) (.inr ())
        (Fintype.card (Level 1 q)) ≤
      ∑ h ∈ range (⌊Sphere.width q (e i)⌋₊+1), ∑ s ∈ T,
        sphereTensor (Sum.elim z (fun _ => s)) (Insertion.energy (Function.update e i h) q) := by
  obtain ⟨k, hk⟩ := recover_wire z i e q hz T hd hT
  let n := Fintype.card (Level 1 q)
  let V₀ := Raw.ofTable (fun j => Level 1 (e j)) (sphereForm z e)
  let V := V₀.pad Unit * Raw.wire F (.inl i) (.inr ()) n
  let J := ℕ × ↥T
  let E (h : ℕ) := Insertion.energy (Function.update e i h) q
  let U (j : J) := Raw.ofTable (fun l => Level 1 (E j.1 l))
    (sphereForm (Sum.elim z (fun _ => j.2.val)) (E j.1))
  let D := range (⌊Sphere.width q (e i)⌋₊+1)
  suffices h : Tensor.ofRaw V ≤ ∑ j ∈ D ×ˢ univ, Tensor.ofRaw (U j) by
    rw [sum_product] at h
    simp only [U, E] at h
    refine h.trans_eq (sum_congr rfl fun j _ => ?_)
    exact sum_coe_sort T (fun s => sphereTensor (Sum.elim z (fun _ => s)) (E j))
  apply (Raw.restriction_sum_iff U V _).mpr
  by_cases h : n = 0
  · refine ⟨fun _ _ _ _ => 0, fun x => ?_⟩
    have hx := ((x (.inr ())).2 : Fin n).isLt
    omega
  have : NeZero n := ⟨h⟩
  let w : Fin n ≃ Level 1 q := (Fintype.equivFin _).symm
  let α (l : A ⊕ Unit) (v : V.leg l) :=
    let t : Fin n := v.2
    if l ∈ ({.inl i, .inr ()} : Finset (A ⊕ Unit)) ∨ t = 0 then (1 : F) else 0
  let f (j : J) (t : Level 1 j.1) : ∀ l, V.leg l → (U j).leg l
    | .inl a, v => selectWord i a t v.1
    | .inr _, v => w v.2
  have hf (j : J) (a b : Level 1 j.1) (l : A ⊕ Unit) (hl : l ≠ .inl i) :
      f j a l = f j b l := by
    cases l with
    | inr _ => rfl
    | inl l =>
      have hn : l ≠ i := fun h => hl (congrArg Sum.inl h)
      funext v
      apply Subtype.ext
      simp [f, selectWord, hn]
  let c (j : J) (t : Level 1 j.1) (v : V.leg (.inl i)) := k j.1 j.2 t v.1 (w v.2)
  choose M hM using fun j => mix_at (U j) V (.inl i) (c j) (f j) (hf j) α
  refine ⟨M, fun x => ?_⟩
  let v : States 1 e := fun j => (x (.inl j)).1
  let b : A ⊕ Unit → Fin n := fun j => (x j).2
  have hV : V.coeff x = (∏ l, α l (x l)) *
      (if w (b (.inl i)) = w (b (.inr ())) then sphereForm z e v else 0) := by
    rw [show V.coeff x = _ from Raw.coeff_mul _ _ x, Raw.pad_coeff]
    change V₀.coeff v * (Raw.wire F (.inl i) (.inr ()) n).coeff b = _
    rw [show V₀.coeff v = _ from Raw.coeff_ofTable _ _ _, wire_coeff]
    change sphereForm z e v * ((∏ l, α l (x l)) * _) = _
    simp only [w.injective.eq_iff, mul_ite, mul_one, mul_zero]
    rw [mul_comm (sphereForm z e v)]
  have hU (j : J) (t : Level 1 j.1) :
      (U j).coeff (fun l => f j t l (x l)) =
        sphereForm (Sum.elim z (fun _ => j.2.val)) (E j.1)
          (Insertion.add (changeAt i v t) (w (b (.inr ())))) := by
    have hl : (fun l => f j t l (x l)) = Insertion.add (changeAt i v t) (w (b (.inr ()))) := by
      funext l
      cases l with
      | inr u => cases u; rfl
      | inl a =>
        change selectWord i a t (v a) = changeAt i v t a
        exact Subtype.ext (changeAt_val i v t a).symm
    rw [hl]
    exact Raw.coeff_ofTable _ _ _
  simp only [hM, hU, ← mul_sum]
  rw [hV, hk, sum_product]

theorem wireProbe (F : Type) [Field F] [Infinite F] : WireProbe F := by
  intro A _ _ _ z hz e i q H
  let N := Fintype.card A * ((∑ j, e j) + H + q)
  obtain ⟨T, ht, hcard⟩ := (Set.finite_range z).infinite_compl.exists_subset_card_eq (1 + N)
  have hd : Disjoint T (Insertion.marks z) := by
    refine disjoint_left.mpr fun s hs he => ht hs ?_
    simpa [Insertion.marks] using he
  exact ⟨T, fun _ h => ht h, hcard.le, probe z hz e i q T hd (show N < T.card by omega)⟩

end OAI.LinearAlgebra.MatrixExponent.Routing
end
