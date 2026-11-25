import OAI.LinearAlgebra.MatrixExponent.Prices.Space
import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Preparation
import OAI.LinearAlgebra.MatrixExponent.Prices.WireRecovery
import Mathlib.Algebra.BigOperators.Field
import OAI.LinearAlgebra.MatrixExponent.Prices.Sync
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryJets

/-!
# A center for prescribed widths

Minimize a smoothed transport cost over ordinary one-site extensions.
Pointwise compactness gives a minimizer. The tangent inequality for
square root makes the same extension minimize a weighted variance.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Center
open Real Spectral Finset

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A]

abbrev Extended (F A : Type) [Field F] [Fintype A] := Tensor F (A ⊕ Unit)

def radius (g : Extended F A →+* ℝ) (i : A) := Tensor.dist g (.inl i) (.inr ())

private theorem minimize (f : Tensor F A →+* ℝ) (hf : Monotone f) (a : A → ℝ) (τ : ℝ) :
    ∃ g : Extended F A →+* ℝ, Monotone g ∧ (∀ T, g (Tensor.pad Unit T) = f T) ∧
      ∀ h : Extended F A →+* ℝ, Monotone h → (∀ T, h (Tensor.pad Unit T) = f T) →
        (∑ i, a i * sqrt (radius g i ^ 2 + τ ^ 2)) ≤ ∑ i, a i * sqrt (radius h i ^ 2 + τ ^ 2) := by
  let T := Extended F A
  let S : Set (T → ℝ) :=
    {v | ∃ g : T →+* ℝ, Monotone g ∧ (∀ t, g (Tensor.pad Unit t) = f t) ∧ ⇑g = v}
  have closed : IsClosed S := by
    have eq : S = {v | v 0 = 0 ∧ v 1 = 1 ∧ (∀ x y, v (x + y) = v x + v y) ∧
        (∀ x y, v (x * y) = v x * v y) ∧ Monotone v ∧ (∀ t, v (Tensor.pad Unit t) = f t)} := by
      ext v
      constructor
      · rintro ⟨g, hg, he, rfl⟩
        exact ⟨g.map_zero, g.map_one, g.map_add, g.map_mul, hg, he⟩
      · rintro ⟨h₀, h₁, ha, hm, hg, he⟩
        exact ⟨{toFun := v, map_zero' := h₀, map_one' := h₁, map_add' := ha, map_mul' := hm},
          hg, he, rfl⟩
    rw [eq]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine (isClosed_eq (continuous_apply 0) continuous_const).inter <|
      (isClosed_eq (continuous_apply 1) continuous_const).inter <|
        IsClosed.inter ?_ (IsClosed.inter ?_ (isClosed_monotone.inter ?_))
    · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (by fun_prop) (by fun_prop)
    · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (by fun_prop) (by fun_prop)
    · exact isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const
  have comp : IsCompact S := by
    choose N hN using fun t : T => Tensor.exists_bound t
    have hc : IsCompact {v : T → ℝ | ∀ t, v t ∈ Set.Icc 0 (N t : ℝ)} :=
      isCompact_pi_infinite fun _ => isCompact_Icc
    refine hc.of_isClosed_subset closed ?_
    rintro v ⟨g, hg, _, rfl⟩ t
    exact ⟨by simpa using hg (Tensor.zero_le t), by simpa using hg (hN t)⟩
  have ne : S.Nonempty := by
    let y (_ : Unit) := Classical.arbitrary A
    exact ⟨_, f.comp (Tensor.foldSites y), hf.comp (Tensor.foldSites_mono y),
      fun t => congrArg f (Tensor.foldSites_pad y t), rfl⟩
  let wire (i : A) : T := Tensor.wire F (.inl i) (.inr ()) 2
  let J (v : T → ℝ) := ∑ i, a i * sqrt ((log (max 1 (v (wire i))) / log 2) ^ 2 + τ ^ 2)
  have cont : Continuous J := by
    apply continuous_finsetSum
    intro i _
    have h : Continuous (fun v : T → ℝ => max 1 (v (wire i))) := by fun_prop
    have hl := h.log (fun _ => (zero_lt_one.trans_le (le_max_left _ _)).ne')
    exact continuous_const.mul (((hl.div_const _).pow 2).add continuous_const).sqrt
  have eval (g : T →+* ℝ) (hg : Monotone g) : J g = ∑ i, a i * sqrt (radius g i ^ 2 + τ ^ 2) := by
    apply sum_congr rfl
    intro i _
    have hw : 1 ≤ g (wire i) := by simpa using hg (Tensor.one_le_wire F (.inl i) (.inr ()) (by decide : 0 < 2))
    rw [max_eq_right hw]
    rfl
  obtain ⟨_, ⟨g, hg, he, rfl⟩, hm⟩ := comp.exists_isMinOn ne cont.continuousOn
  refine ⟨g, hg, he, fun h hh he' => ?_⟩
  rw [← eval g hg, ← eval h hh]
  exact hm ⟨h, hh, he', rfl⟩

private def smooth (τ d : ℝ) := sqrt (d ^ 2 + τ ^ 2)

private theorem smooth_sq (τ d : ℝ) : smooth τ d ^ 2 = d ^ 2 + τ ^ 2 := sq_sqrt (by positivity)

private theorem smooth_bounds {τ d : ℝ} (ht : 0 < τ) (ht' : τ ≤ 1) (hd : 0 ≤ d) (hd' : d ≤ 1) :
    τ ≤ smooth τ d ∧ smooth τ d ≤ 2 ∧ d + τ ^ 2 / 3 ≤ smooth τ d := by
  have hs : 0 ≤ smooth τ d := sqrt_nonneg _
  have h := smooth_sq τ d
  have hu : smooth τ d ≤ 2 := by nlinarith
  have hl : d ≤ smooth τ d := by nlinarith
  refine ⟨by nlinarith, hu, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ 3 - (smooth τ d + d) by linarith)]

private theorem tangent {a τ d μ : ℝ} (hp : 0 < μ) (hμ : a * μ ^ 2 = smooth τ d) (x : ℝ) :
    2 * (a * smooth τ x - a * smooth τ d) ≤ (x / μ) ^ 2 - (d / μ) ^ 2 := by
  rw [div_pow, div_pow, ← sub_div, le_div_iff₀ (sq_pos_of_pos hp)]
  have he : 2 * (a * smooth τ x - a * smooth τ d) * μ ^ 2 =
      2 * smooth τ d * (smooth τ x - smooth τ d) := by rw [← hμ]; ring
  rw [he]
  nlinarith only [sq_nonneg (smooth τ x - smooth τ d), smooth_sq τ x, smooth_sq τ d]

private theorem lower {a τ d μ : ℝ} (hp : 0 < μ) (hμ : a * μ ^ 2 = smooth τ d)
    (ht : 0 < τ) (ht' : τ ≤ 1) (hd : 0 ≤ d) (hd' : d ≤ 1) :
    a * d - τ * a ≤ (d / μ) ^ 2 := by
  obtain ⟨h₁, _, h₂⟩ := smooth_bounds ht ht' hd hd'
  have hs : d ≤ smooth τ d := by nlinarith
  rw [div_pow, le_div_iff₀ (sq_pos_of_pos hp)]
  have he : (a * d - τ * a) * μ ^ 2 = (d - τ) * smooth τ d := by rw [← hμ]; ring
  rw [he]
  nlinarith only [smooth_sq τ d, mul_le_mul_of_nonneg_left h₁ ht.le,
    mul_le_mul_of_nonneg_right hs (ht.le.trans h₁)]

/-- A common positive compact range of weights works for every
ordinary spectral point. -/
theorem choose_weights (a : A → ℝ) (ha : ∀ i, 0 < a i) {τ : ℝ} (ht : 0 < τ) (ht' : τ ≤ 1) :
    ∃ l U : ℝ, 0 < l ∧ 0 < U ∧ ∀ f : Tensor F A →+* ℝ, Monotone f →
      ∃ g : Extended F A →+* ℝ, Monotone g ∧ (∀ t, g (Tensor.pad Unit t) = f t) ∧
        ∃ μ : A → ℝ, (∀ i, l ≤ μ i ∧ μ i ≤ U) ∧
          (∀ i, radius g i + τ ^ 2 / 3 ≤ a i * μ i ^ 2) ∧
          (∑ i, a i * radius g i) - τ * (∑ i, a i) ≤ ∑ i, (radius g i / μ i) ^ 2 ∧
          ∀ h : Extended F A →+* ℝ, Monotone h → (∀ t, h (Tensor.pad Unit t) = f t) →
            (∑ i, (radius g i / μ i) ^ 2) ≤ ∑ i, (radius h i / μ i) ^ 2 := by
  obtain ⟨j, _, hj⟩ := univ.exists_min_image a univ_nonempty
  obtain ⟨k, _, hk⟩ := univ.exists_max_image a univ_nonempty
  refine ⟨sqrt (τ / a k), sqrt (2 / a j), sqrt_pos.mpr (div_pos ht (ha k)),
    sqrt_pos.mpr (div_pos (by norm_num) (ha j)), fun f hf => ?_⟩
  obtain ⟨g, hg, he, hm⟩ := minimize f hf a τ
  let d := radius g
  have h₀ (i : A) : 0 ≤ d i := Tensor.dist_nonneg g hg _ _
  have h₁ (i : A) : d i ≤ 1 := Tensor.dist_le_one g hg _ _
  have hs (i : A) := smooth_bounds ht ht' (h₀ i) (h₁ i)
  let μ (i : A) := sqrt (smooth τ (d i) / a i)
  have hp (i : A) : 0 < smooth τ (d i) / a i := div_pos (ht.trans_le (hs i).1) (ha i)
  have hμ (i : A) : a i * μ i ^ 2 = smooth τ (d i) := by
    unfold μ
    rw [sq_sqrt (hp i).le, mul_div_cancel₀ _ (ha i).ne']
  refine ⟨g, hg, he, μ, fun i => ?_, fun i => ?_, ?_, fun h hh he' => ?_⟩
  · constructor
    · exact sqrt_le_sqrt (div_le_div₀ (ht.le.trans (hs i).1) (hs i).1 (ha i) (hk i (mem_univ i)))
    · exact sqrt_le_sqrt (div_le_div₀ (by norm_num) (hs i).2.1 (ha j) (hj i (mem_univ i)))
  · rw [hμ]
    exact (hs i).2.2
  · rw [mul_sum, ← sum_sub_distrib]
    exact sum_le_sum fun i _ => lower (sqrt_pos.mpr (hp i)) (hμ i) ht ht' (h₀ i) (h₁ i)
  · have hi := sum_le_sum (fun i (_ : i ∈ univ) =>
      tangent (sqrt_pos.mpr (hp i)) (hμ i) (radius h i))
    rw [← mul_sum, sum_sub_distrib, sum_sub_distrib] at hi
    have hmin : (∑ i, a i * smooth τ (d i)) ≤ ∑ i, a i * smooth τ (radius h i) := hm h hh he'
    exact sub_nonneg.mp ((mul_nonneg (by norm_num) (sub_nonneg.mpr hmin)).trans hi)

end OAI.LinearAlgebra.MatrixExponent.Routing.Center
end

/-!
# Weighted quadratic budgets

A transport bound implies coercivity, hence a maximizing nonzero form at
every positive scale. The normalized deficit dominates the sum of squared
distances of the rescaled widths from their targets.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Budget
open Sphere Spectral Filter Finset

variable {A F : Type} [Fintype A] [Field F]

def value (p : (A → ℕ) → ℝ) (μ : A → ℝ) (n : ℕ) (e : A → ℕ) : ℝ :=
  p e - (∑ i, (μ i * Routing.width (e i)) ^ 2) / (2 * n)

variable {p : (A → ℕ) → ℝ} {μ r : A → ℝ}

theorem normalize (n : ℕ) (e : A → ℕ) :
    value p μ n e / n = p e / n - (∑ i, (μ i * Routing.width (e i) / n) ^ 2) / 2 := by
  unfold value
  simp only [div_pow, ← sum_div]
  ring

theorem increment (e : A → ℕ) (n : ℕ) (hn : 0 < n) :
    (∑ i, (μ i * Routing.width (e i) / n) ^ 2) * ((n : ℝ) / (n + 1)) =
      2 * (value p μ (n + 1) e - value p μ n e) := by
  simp only [value, div_pow, ← sum_div, Nat.cast_add, Nat.cast_one]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

variable (ht : ∀ e, p e ≤ ∑ i, r i * (μ i * Routing.width (e i)))
include ht

theorem squares (n : ℕ) (e : A → ℕ) :
    2 * (value p μ n e / n) + ∑ i, (μ i * Routing.width (e i) / n - r i) ^ 2 ≤ ∑ i, r i ^ 2 := by
  rw [normalize]
  have hb : p e / n ≤ ∑ i, r i * (μ i * Routing.width (e i) / n) := by
    simp only [← mul_div_assoc, ← sum_div]
    exact div_le_div_of_nonneg_right (ht e) (by positivity)
  have he : (∑ i, (μ i * Routing.width (e i) / n - r i) ^ 2) =
      (∑ i, (μ i * Routing.width (e i) / n) ^ 2) -
        2 * (∑ i, r i * (μ i * Routing.width (e i) / n)) + ∑ i, r i ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  linarith only [he, hb]

variable {D l : ℝ} (hD : ∑ i, r i ^ 2 ≤ D) (hl : 0 < l) (hμ : ∀ i, l ≤ μ i)
include hD hl hμ

theorem bounds (n : ℕ) (hn : 0 < n) (e : A → ℕ) (he : 0 ≤ value p μ n e) (i : A) :
    μ i * Routing.width (e i) / n ≤ 2 * (D + 1) ∧
      (e i : ℝ) ≤ (4 * (D + 1) / (l * entropy) ^ 2) * (n : ℝ) ^ 2 := by
  have hs := (squares ht n e).trans hD
  have hp : 0 ≤ value p μ n e / n := div_nonneg he (by positivity)
  have hd := (single_le_sum (fun j (_ : j ∈ univ) => sq_nonneg (r j)) (mem_univ i)).trans hD
  have hw := single_le_sum (fun j (_ : j ∈ univ) => sq_nonneg (μ j * Routing.width (e j) / n - r j))
    (mem_univ i)
  have hb : (μ i * Routing.width (e i) / (n : ℝ)) ^ 2 ≤ 4 * D := by
    nlinarith only [hs, hp, hd, hw, sq_nonneg (μ i * Routing.width (e i) / n - 2 * r i)]
  constructor
  · nlinarith only [hb, sq_nonneg (μ i * Routing.width (e i) / n - 1)]
  · rw [div_pow, mul_pow, width_sq, div_le_iff₀ (by positivity)] at hb
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos (mul_pos hl entropy_pos))]
    have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl.le (hμ i) 2)
      (show 0 ≤ entropy ^ 2 * (e i : ℝ) by positivity)
    nlinarith only [hb, h, sq_nonneg (n : ℝ)]

theorem maximizer (z : A → F) (hp : 0 ≤ p (fun _ => 0))
    (hzero : ∀ e, sphereForm z e = 0 → p e = 0) (n : ℕ) :
    ∃ e : A → ℕ, 0 < n → 0 ≤ value p μ n e ∧ sphereForm z e ≠ 0 ∧
      ∀ a, value p μ n a ≤ value p μ n e := by
  by_cases hn : 0 < n
  swap
  · exact ⟨fun _ => 0, fun hh => (hn hh).elim⟩
  let N := ⌊(4 * (D + 1) / (l * entropy) ^ 2) * (n : ℝ) ^ 2⌋₊
  let S := {e | 0 ≤ value p μ n e ∧ sphereForm z e ≠ 0}
  have hS : S.Finite := by
    apply (Set.Finite.pi' (fun _ : A => Set.finite_Iic N)).subset
    exact fun e he i => Nat.le_floor (bounds ht hD hl hμ n hn e he.1 i).2
  have he : S.Nonempty := by
    refine ⟨fun _ => 0, ?_, sphereForm_vacuum z⟩
    simpa [value, Routing.width] using hp
  obtain ⟨e, ⟨hpos, hne⟩, hmax⟩ := S.exists_max_image (value p μ n) hS he
  refine ⟨e, fun _ => ⟨hpos, hne, fun a => ?_⟩⟩
  by_cases ha : 0 ≤ value p μ n a
  swap
  · exact (le_of_not_ge ha).trans hpos
  by_cases hz : sphereForm z a = 0
  · refine le_trans ?_ hpos
    rw [value, hzero a hz, zero_sub, neg_nonpos]
    exact div_nonneg (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
  · exact hmax _ ⟨ha, hz⟩

end OAI.LinearAlgebra.MatrixExponent.Routing.Budget
end

/-!
# Distance tests from a synchronized extension and wire recovery

Use the same extended price for all site probes. A cubic energy cutoff
absorbs the bounded quadratic optimizer budgets. The logarithm of the
polynomial overhead in the recovered wire is then logarithmic in the
optimizer scale.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Sphere Spectral Real Filter Finset

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A]
  {Y : Type*} [MetricSpace Y]

theorem probe_cost (R : ℝ) (hR : 0 < R) {n a q : ℕ} (hn : 1 ≤ (n : ℝ))
    (ha : (a : ℝ) ≤ R * n ^ 2) (hq : q ≤ n) :
    Sphere.width q a ≤ (sqrt R + 2) ^ 2 * (n : ℝ) ^ 2 ∧
      entropy ^ 2 * (Sphere.width q a + q - a) ≤
        2 * width a * width q + entropy ^ 2 * (sqrt R + 3) * n := by
  have hnq : (q : ℝ) ≤ n := by exact_mod_cast hq
  have hs : sqrt (a : ℝ) ≤ sqrt R * n :=
    sqrt_le_iff.mpr ⟨by positivity, by rwa [mul_pow, sq_sqrt hR.le]⟩
  have ht : sqrt (q : ℝ) ≤ (n : ℝ) := sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hh := pow_le_pow_left₀ (show 0 ≤ sqrt (q : ℝ) + sqrt (a : ℝ) + 1 by positivity)
    (show sqrt (q : ℝ) + sqrt (a : ℝ) + 1 ≤ (sqrt R + 2) * n by linarith) 2
  unfold Sphere.width
  constructor
  · nlinarith only [hh, sqrt_nonneg q, sqrt_nonneg a]
  · have hk : (sqrt q + sqrt a) ^ 2 + (sqrt q + sqrt a) + q - a ≤
        2 * sqrt a * sqrt q + (sqrt R + 3) * n := by
      nlinarith only [sq_sqrt (Nat.cast_nonneg q), sq_sqrt (Nat.cast_nonneg a), hnq, hs, ht]
    unfold width
    linarith only [mul_le_mul_of_nonneg_left hk (sq_nonneg entropy)]

omit [DecidableEq A] in
private theorem value_pos {f : Tensor F A →+* ℝ} (hf : Monotone f) {z : A → F} {e : A → ℕ}
    (he : sphereForm z e ≠ 0) : 0 < f (sphereTensor z e) := by
  refine zero_lt_one.trans_le (Tensor.value_one_le hf ?_)
  intro ht
  apply he
  funext v
  simpa using (Tensor.ofRaw_eq_zero _).mp ht v

omit [DecidableEq A] in
private theorem objective_eq (f : Tensor F A →+* ℝ) (d : ℝ) (z : A → F) (n : ℕ) (e : A → ℕ) :
    objective (Tensor.values d f) z n e =
      d * log (f (sphereTensor z e)) - entropy ^ 2 / (2 * n) * ∑ i, (e i : ℝ) := by
  simp only [objective, spherePrice, tablePrice, Tensor.values, width_sq, ← mul_sum]
  rw [mul_assoc, div_mul_cancel₀ _ (log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  unfold sphereTensor
  ring

omit [Nonempty A] in
private theorem sum_added (t : A ⊕ Unit → ℝ) (e : A → ℕ) (i : A) (h q : ℕ) :
    ∑ j : A ⊕ Unit, t j * ((Sum.elim (Function.update e i h) (fun _ => q) j : ℕ) : ℝ) =
      (∑ j, t (.inl j) * (e j : ℝ)) - t (.inl i) * e i + t (.inl i) * h + t (.inr ()) * q := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
  rw [← sum_erase_add _ _ (mem_univ i), ← sum_erase_add _ (fun j => t (.inl j) * (e j : ℝ)) (mem_univ i)]
  have he : ∑ j ∈ univ.erase i, t (.inl j) * ((Function.update e i h j : ℕ) : ℝ) = ∑ j ∈ univ.erase i, t (.inl j) * (e j : ℝ) :=
    sum_congr rfl (fun j hj => by rw [Function.update_of_ne (mem_erase.mp hj).1])
  rw [he, Function.update_self, add_sub_cancel_right]

theorem probe_log (hW : WireProbe F) {f : Tensor F A →+* ℝ} (hf : Monotone f)
    {g : Tensor F (A ⊕ Unit) →+* ℝ} (hg : Monotone g) (hgf : ∀ T, g (Tensor.pad Unit T) = f T)
    {z : A → F} (hz : Function.Injective z) (B : ℝ) (t : A ⊕ Unit → ℝ) (ht : ∀ i, 0 ≤ t i) (M : ℕ)
    (hg' : ∀ s ∉ Set.range z, ∀ e : A ⊕ Unit → ℕ, (∀ j, e j ≤ M) →
      g (sphereTensor (Sum.elim z (fun _ => s)) e) ≤
        ((M : ℝ) + 2) ^ (Fintype.card A + 8) * exp (B + ∑ j, t j * (e j : ℝ)))
    (e : A → ℕ) (he : sphereForm z e ≠ 0) (i : A) (q : ℕ)
    (hA : Fintype.card A ≤ M) (heM : ∀ j, e j ≤ M)
    (hH : ⌊Sphere.width q (e i)⌋₊ ≤ M) (hq : q ≤ M) (hq' : 0 < Fintype.card (Level 1 q)) :
    log (f (sphereTensor z e)) + Tensor.dist g (.inl i) (.inr ()) * log (Fintype.card (Level 1 q)) ≤
      (Fintype.card A + 12) * log (M + 2) + B + ((∑ j, t (.inl j) * (e j : ℝ)) - t (.inl i) * e i +
        t (.inl i) * Sphere.width q (e i) + t (.inr ()) * q) := by
  let H := ⌊Sphere.width q (e i)⌋₊
  let p := (M : ℝ) + 2
  let b := B + ((∑ j, t (.inl j) * (e j : ℝ)) - t (.inl i) * e i +
        t (.inl i) * Sphere.width q (e i) + t (.inr ()) * q)
  let D := Fintype.card A + 8
  have hp : 0 < p := by unfold p; positivity
  obtain ⟨T, hT, hcard, hw⟩ := hW A z hz e i q
  have hTC : (T.card : ℝ) ≤ p ^ 3 := by
    have hs : (∑ j, e j) ≤ M * M := calc
      _ ≤ Fintype.card A * M := by simpa using sum_le_card_nsmul univ e M (fun j _ => heM j)
      _ ≤ M * M := Nat.mul_le_mul_right M hA
    have hc : T.card ≤ (M + 2) ^ 3 := calc
      _ ≤ 1 + M * (M * M + M + M) := hcard.trans (by gcongr)
      _ ≤ _ := by ring_nf; omega
    unfold p
    exact_mod_cast hc
  let X (h : ℕ) (s : F) : Tensor F (A ⊕ Unit) := sphereTensor (Sum.elim z (fun _ => s))
    (Sum.elim (Function.update e i h) (fun _ => q))
  have hs (h : ℕ) (hh : h ∈ range (H + 1)) (s : F) (hs : s ∈ T) : g (X h s) ≤ p ^ D * exp b := by
    have hle := Nat.le_of_lt_succ (mem_range.mp hh)
    have hle' : (h : ℝ) ≤ Sphere.width q (e i) :=
      (Nat.cast_le.mpr hle).trans (Nat.floor_le (by unfold Sphere.width; positivity))
    apply (hg' s (hT s hs) _ ?_).trans
    · rw [sum_added]
      unfold p D b
      gcongr
      exact ht _
    · rintro (j | _)
      · change Function.update e i h j ≤ M
        by_cases hji : j = i
        · simpa [hji] using hle.trans hH
        · simpa [hji] using heM j
      · exact hq
  have hh : (H : ℝ) + 1 ≤ p := by unfold p; exact_mod_cast (show H + 1 ≤ M + 2 by omega)
  have hw' : f (sphereTensor z e) * (Fintype.card (Level 1 q) : ℝ) ^ Tensor.dist g (.inl i) (.inr ()) ≤
      p ^ (D + 4) * exp b := by
    calc
      _ ≤ ∑ h ∈ range (H + 1), ∑ s ∈ T, g (X h s) := by
        have hb := hg hw
        rw [g.map_mul, hgf, Tensor.price_wire g hg _ _ hq'] at hb
        simpa only [map_sum] using hb
      _ ≤ ∑ _ ∈ range (H + 1), ∑ _ ∈ T, p ^ D * exp b :=
        sum_le_sum (fun h hh => sum_le_sum (hs h hh))
      _ = ((H : ℝ) + 1) * (T.card * (p ^ D * exp b)) := by simp
      _ ≤ p * (p ^ 3 * (p ^ D * exp b)) := by gcongr
      _ = _ := by rw [pow_add]; ring
  have h₁ := value_pos hf he
  have h₂ : (0 : ℝ) < Fintype.card (Level 1 q) := by exact_mod_cast hq'
  have h := log_le_log (by positivity) hw'
  rw [log_mul (by positivity) (by positivity), log_rpow h₂, log_mul (by positivity) (by positivity),
    log_pow, log_exp] at h
  unfold p D b at h
  push_cast at h
  linarith only [h]

theorem probe_window (R : ℝ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) ∧ 1 ≤ log n ∧ ∃ M : ℕ, n ≤ M ∧ k ≤ M ∧
      (sqrt R + 2) ^ 2 * (n : ℝ) ^ 2 ≤ M ∧ log ((M : ℝ) + 2) ≤ 4 * log n := by
  filter_upwards [eventually_ge_atTop (k), eventually_ge_atTop 2,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop ((sqrt R + 2) ^ 2),
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with n hnA hn₂ hnR hnlog
  have hn : 0 < (n : ℝ) := by positivity
  have hn' : 2 ≤ (n : ℝ) := by exact_mod_cast hn₂
  let M := n ^ 3
  have hnM : n ≤ M := Nat.le_self_pow (by decide) _
  have hcap : (sqrt R + 2) ^ 2 * (n : ℝ) ^ 2 ≤ M := by
    unfold M
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_right hnR (sq_nonneg (n : ℝ))]
  have hlog : log ((M : ℝ) + 2) ≤ 4 * log n := by
    have h : (M : ℝ) + 2 ≤ (n : ℝ) ^ 4 := by
      have := (Nat.cast_le (α := ℝ)).mpr hnM
      unfold M at this ⊢
      push_cast at this ⊢
      nlinarith only [mul_le_mul_of_nonneg_right hn' (pow_nonneg hn.le 3), hn', this]
    simpa using log_le_log (by positivity) h
  exact ⟨by linarith, hnlog, M, hnM, hnA.trans hnM, hcap, hlog⟩

theorem controlled_of_probes (hV : VarianceTest F Y) (hE : BoundedExtension F)
    (hW : WireProbe F) (hS : SpectralSpace F Y) : Controlled F Y := by
  intro A _ _ _ x o ho z hz
  by_cases hzero : (∑ i, dist o (x i) ^ 2) ≤ 0
  · obtain ⟨P, _, hp⟩ := hS A x
    refine ⟨P, hp, fun _ _ => ⟨0, ?_⟩⟩
    filter_upwards with n
    intro e _ _ _
    refine ⟨fun _ => 0, fun _ => le_rfl, by simpa using hzero, fun i g _ => ?_⟩
    simp only [zero_mul, add_zero]
    exact div_nonneg (mul_nonneg (width_nonneg _) (width_nonneg _)) (by positivity)
  let i₀ : A := Classical.arbitrary A
  have : Nontrivial A := by
    by_contra hn
    have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hn
    have hx (i : A) : x i = x i₀ := congrArg x (Subsingleton.elim _ _)
    have hy := ho (x i₀)
    simp [hx] at hy
    exact hzero (by simp [hx, hy])
  obtain ⟨d, hd, f, hf, hP, hvar⟩ := hV A x o ho
  have hd' : 0 < d := by
    rcases hd.eq_or_lt with hd | hd
    · let y (_ : Unit) := i₀
      have hh := hvar (f.comp (Tensor.foldSites y)) (hf.comp (Tensor.foldSites_mono y))
        (fun T => congrArg f (Tensor.foldSites_pad y T))
      exact (hzero (by simpa [← hd] using hh)).elim
    · exact hd
  refine ⟨Tensor.values d f, hP, fun R hR => ?_⟩
  let c := entropy ^ 2 * (sqrt R + 3) / 2
  let C := d * (Fintype.card A + 12) * 4 + c
  have hc : 0 ≤ c := by unfold c; positivity
  have hC : 0 ≤ C := by unfold C; positivity
  refine ⟨C, ?_⟩
  filter_upwards [probe_window R (Fintype.card A)] with n hn
  intro e he hbudget hne
  obtain ⟨hn', hnlog, M, hnM, hA, hcap, hlog⟩ := hn
  have hn : 0 < (n : ℝ) := zero_lt_one.trans_le hn'
  have heM (i : A) : e i ≤ M := by
    have h : R ≤ (sqrt R + 2) ^ 2 := by nlinarith [sq_sqrt hR.le, sqrt_nonneg R]
    exact Nat.cast_le.mp ((hbudget i).trans ((mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans hcap))
  let B := objective (Tensor.values d f) z n e / d
  let t := entropy ^ 2 / (2 * n) / d
  have ht : 0 ≤ t := by unfold t; positivity
  have hdt : d * t = entropy ^ 2 / (2 * n) := mul_div_cancel₀ _ hd'.ne'
  have hB : d * B = objective (Tensor.values d f) z n e := mul_div_cancel₀ _ hd'.ne'
  have hbase (a : A → ℕ) : f (sphereTensor z a) ≤ exp (B + ∑ i, t * (a i : ℝ)) := by
    apply le_exp_of_log_le
    apply (mul_le_mul_iff_right₀ hd').mp
    rw [← mul_sum, mul_add, hB, ← mul_assoc, hdt]
    have := he a
    rw [objective_eq] at this
    linarith only [this]
  obtain ⟨g, hg, hgf, htest⟩ := hE A f hf z hz B t ht hbase M
  refine ⟨fun i => d * Tensor.dist g (.inl i) (.inr ()),
    fun i => mul_nonneg hd (Tensor.dist_nonneg g hg _ _), hvar g hg hgf, fun i q hq => ?_⟩
  by_cases hq' : 0 < Fintype.card (Level 1 q)
  swap
  · rw [Nat.eq_zero_of_not_pos hq', Nat.cast_zero, log_zero, mul_zero]
    exact add_nonneg (div_nonneg (mul_nonneg (width_nonneg _) (width_nonneg _)) hn.le)
      (mul_nonneg hC (zero_le_one.trans hnlog))
  obtain ⟨hlim, hw⟩ := probe_cost R hR (by linarith : 1 ≤ (n : ℝ)) (hbudget i) hq
  have hH : ⌊Sphere.width q (e i)⌋₊ ≤ M := by
    exact Nat.cast_le.mp ((Nat.floor_le (by unfold Sphere.width; positivity)).trans (hlim.trans hcap))
  have hp := probe_log hW hf hg hgf hz B (fun _ => t) (fun _ => ht) M htest e hne i q hA heM hH
    (hq.trans hnM) hq'
  simp only [← mul_sum, ← mul_sub, ← mul_add] at hp
  have hp' := mul_le_mul_of_nonneg_left hp hd
  rw [mul_add, mul_add, mul_add, hB, objective_eq, ← mul_assoc d t, hdt] at hp'
  have hh : entropy ^ 2 / (2 * n) * (Sphere.width q (e i) + q - e i) ≤
      width (e i) * width q / n + c := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    unfold c
    refine hw.trans_eq ?_
    field_simp
  have hl := mul_le_mul_of_nonneg_left hlog (show 0 ≤ d * (Fintype.card A + 12) by positivity)
  have he' := mul_le_mul_of_nonneg_left hnlog hc
  unfold C
  linarith only [hp', hh, hl, he']

end OAI.LinearAlgebra.MatrixExponent.Routing
end

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral

/-- A price extension with a separate energy penalty at each site. -/
def WeightedExtension (F : Type) [Field F] : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] (f : Tensor F A →+* ℝ),
    Monotone f → ∀ z : A → F, Function.Injective z →
    ∀ (B : ℝ) (t : A ⊕ Unit → ℝ), (∀ i, 0 ≤ t i ∧ t i ≤ t (.inr ())) →
    (∀ e, f (sphereTensor z e) ≤ Real.exp (B + ∑ i, t (.inl i) * (e i : ℝ))) →
    ∀ M : ℕ, ∃ g : Tensor F (A ⊕ Unit) →+* ℝ, Monotone g ∧
      (∀ T, g (Tensor.pad Unit T) = f T) ∧
      ∀ (s : F), s ∉ Set.range z → ∀ e : A ⊕ Unit → ℕ, (∀ i, e i ≤ M) →
        g (sphereTensor (Sum.elim z (fun _ => s)) e) ≤
          ((M : ℝ) + 2) ^ (Fintype.card A + 8) * Real.exp (B + ∑ i, t i * (e i : ℝ))

theorem WeightedExtension.uniform {F : Type} [Field F] (h : WeightedExtension F) :
    BoundedExtension F := by
  intro A _ _ _ f hf z hz B t ht
  exact h A f hf z hz B (fun _ => t) (fun _ => ⟨ht, le_rfl⟩)

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Uniform distance tests for weighted budgets

Penalties are squared rescaling factors. The new site pays the largest
allowed penalty. Since its probe energy is at most the optimizer scale,
this adds only a bounded term to the logarithmic error.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Center
open Spectral Real Filter Finset Sphere

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A]

def price (f : Tensor F A →+* ℝ) (z : A → F) (e : A → ℕ) := log (f (sphereTensor z e))

private def penalty (μ : A → ℝ) (U : ℝ) (n : ℕ) (i : A ⊕ Unit) :=
  (Sum.elim μ (fun _ => U) i) ^ 2 * entropy ^ 2 / (2 * n)

omit [DecidableEq A] in
private theorem value_eq (f : Tensor F A →+* ℝ) (z : A → F) (μ : A → ℝ)
    (U : ℝ) (n : ℕ) (e : A → ℕ) :
    Budget.value (price f z) μ n e =
      log (f (sphereTensor z e)) - ∑ i, penalty μ U n (.inl i) * (e i : ℝ) := by
  unfold Budget.value price
  rw [sum_div]
  congr 1
  apply sum_congr rfl
  intro i _
  simp only [penalty, Sum.elim_inl, mul_pow, width_sq]
  ring

private theorem weighted_cost (R U v : ℝ) (hR : 0 < R) (hv : 0 < v) (hU : v ≤ U)
    {n a q : ℕ} (hn : 1 ≤ (n : ℝ)) (ha : (a : ℝ) ≤ R * n ^ 2) (hq : q ≤ n) :
    v ^ 2 * entropy ^ 2 / (2 * n) * (Sphere.width q a - a) + U ^ 2 * entropy ^ 2 / (2 * n) * q ≤
      v ^ 2 * Routing.width a * Routing.width q / n + U ^ 2 * entropy ^ 2 * (sqrt R + 4) := by
  have hc := (probe_cost R hR hn ha hq).2
  have hn' : 0 < (n : ℝ) := zero_lt_one.trans_le hn
  have h₁ := mul_le_mul_of_nonneg_left hc (sq_nonneg v)
  have h₂ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv.le hU 2)
    (show 0 ≤ entropy ^ 2 * (sqrt R + 3) * n by positivity)
  have h₃ := mul_le_mul_of_nonneg_left (show (q : ℝ) ≤ n by exact_mod_cast hq)
    (show 0 ≤ U ^ 2 * entropy ^ 2 by positivity)
  have h₄ : 0 ≤ v ^ 2 * entropy ^ 2 * q := by positivity
  have h₅ : 0 ≤ U ^ 2 * entropy ^ 2 * (sqrt R + 4) * n := by positivity
  field_simp
  linarith only [h₁, h₂, h₃, h₄, h₅]

theorem weighted_control (hE : WeightedExtension F) (hW : WireProbe F)
    (z : A → F) (hz : Function.Injective z) {l U R : ℝ} (hl : 0 < l) (hR : 0 < R) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ (f : Tensor F A →+* ℝ), Monotone f →
      ∀ μ : A → ℝ, (∀ i, l ≤ μ i ∧ μ i ≤ U) → ∀ e : A → ℕ,
      (∀ a, Budget.value (price f z) μ n a ≤ Budget.value (price f z) μ n e) →
      (∀ i, (e i : ℝ) ≤ R * (n : ℝ) ^ 2) → sphereForm z e ≠ 0 →
      ∃ g : Extended F A →+* ℝ, Monotone g ∧ (∀ T, g (Tensor.pad Unit T) = f T) ∧
        ∀ i q, q ≤ n → radius g i / μ i * log (Fintype.card (Level 1 q)) ≤
          μ i * Routing.width (e i) / n * entropy * sqrt q + C * log n := by
  let c := U ^ 2 * entropy ^ 2 * (sqrt R + 4)
  let C := ((Fintype.card A + 12) * 4 + c) / l
  have hc : 0 ≤ c := by unfold c; positivity
  have hC : 0 ≤ C := by unfold C; positivity
  refine ⟨C, ?_⟩
  filter_upwards [probe_window R (Fintype.card A)] with n hn
  obtain ⟨hn, hnlog, M, hnM, hA, hcap, hlog⟩ := hn
  intro f hf μ hμ e he hbudget hne
  have hμpos i := hl.trans_le (hμ i).1
  let t := penalty μ U n
  have ht (i) : 0 ≤ t i ∧ t i ≤ t (.inr ()) := by
    refine ⟨by unfold t penalty; positivity, ?_⟩
    cases i with
    | inr i => rfl
    | inl i =>
      simp only [t, penalty, Sum.elim_inl, Sum.elim_inr]
      have := hμpos i
      gcongr
      exact (hμ i).2
  let B := Budget.value (price f z) μ n e
  have hbase (a : A → ℕ) : f (sphereTensor z a) ≤ exp (B + ∑ i, t (.inl i) * (a i : ℝ)) := by
    apply le_exp_of_log_le
    apply sub_le_iff_le_add.mp
    rw [← value_eq f z μ U n a]
    exact he a
  obtain ⟨g, hg, hgf, htest⟩ := hE A f hf z hz B t ht hbase M
  refine ⟨g, hg, hgf, fun i q hq => ?_⟩
  have hw := width_nonneg (e i)
  have hm := hμpos i
  have h₀ := entropy_pos
  by_cases hq' : 0 < Fintype.card (Level 1 q)
  swap
  · rw [Nat.eq_zero_of_not_pos hq', Nat.cast_zero, log_zero, mul_zero]
    positivity
  have heM (j : A) : e j ≤ M := by
    have h : R ≤ (sqrt R + 2) ^ 2 := by nlinarith [sq_sqrt hR.le, sqrt_nonneg R]
    exact Nat.cast_le.mp ((hbudget j).trans ((mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans hcap))
  have hlim := (probe_cost R hR hn (hbudget i) hq).1
  have hH : ⌊Sphere.width q (e i)⌋₊ ≤ M :=
    Nat.cast_le.mp ((Nat.floor_le (by unfold Sphere.width; positivity)).trans (hlim.trans hcap))
  have hp := probe_log hW hf hg hgf hz B t (fun i => (ht i).1) M htest e hne i q hA heM hH
    (hq.trans hnM) hq'
  unfold B at hp
  rw [value_eq f z μ U n e] at hp
  have hh := weighted_cost R U (μ i) hR hm (hμ i).2 hn (hbudget i) hq
  have hcoeff : (Fintype.card A + 12) * 4 + c ≤ μ i * C :=
    (mul_div_cancel₀ _ hl.ne').symm.le.trans (mul_le_mul_of_nonneg_right (hμ i).1 hC)
  have hk := mul_le_mul_of_nonneg_right hcoeff (zero_le_one.trans hnlog)
  have hcost := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (Fintype.card A : ℝ) + 12 by positivity)
  have herr := mul_le_mul_of_nonneg_left hnlog hc
  rw [div_mul_eq_mul_div, div_le_iff₀ hm, mul_assoc _ entropy, ← Routing.width]
  unfold radius
  simp only [t, penalty, Sum.elim_inl, Sum.elim_inr] at hp
  unfold c at herr hk
  simp only [div_eq_mul_inv] at hp hh ⊢
  linarith only [hp, hh, hk, hcost, herr]

end OAI.LinearAlgebra.MatrixExponent.Routing.Center
end

/-!
# Uniform prescribed widths

A smoothed minimizing extension sets the weights of the quadratic
optimization. Its strict slack absorbs the uniform error in the
optimizing widths. The price and width bounds use natural logarithms.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Sphere Spectral Filter Finset Center

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A]

private theorem transport_bound (f : Tensor F A →+* ℝ) (g : Extended F A →+* ℝ)
    (hg : Monotone g) (hgf : ∀ T, g (Tensor.pad Unit T) = f T)
    (z : A → F) (μ : A → ℝ) (hμ : ∀ i, 0 < μ i) (e : A → ℕ) :
    price f z e ≤ ∑ i, (radius g i / μ i) * (μ i * width (e i)) := by
  have h := Tensor.preparation hg (Raw.ofTable (fun i => Level 1 (e i)) (sphereForm z e))
  rw [hgf] at h
  apply h.trans
  apply sum_le_sum
  intro i _
  rw [← mul_assoc, div_mul_cancel₀ _ (hμ i).ne']
  exact mul_le_mul_of_nonneg_left (entropy_bound _) (Tensor.dist_nonneg g hg _ _)

omit [DecidableEq A] in
private theorem cost_zero (f : Tensor F A →+* ℝ) (z : A → F) (e : A → ℕ)
    (h : sphereForm z e = 0) : price f z e = 0 := by
  have ht : sphereTensor z e = 0 := by
    refine (Tensor.ofRaw_eq_zero _).mpr ?_
    change ∀ v : States 1 e, (Raw.ofTable (fun i => Level 1 (e i)) (sphereForm z e)).coeff v = 0
    simp [h]
  simp [price, ht]

/-- Uniformity in both the price and a compact range of penalties. -/
private theorem profile (hE : WeightedExtension F) (hW : WireProbe F) (z : A → F)
    (hz : Function.Injective z) {l U η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ (f : Tensor F A →+* ℝ), Monotone f →
      ∀ (g : Extended F A →+* ℝ), Monotone g → (∀ T, g (Tensor.pad Unit T) = f T) →
      ∀ μ : A → ℝ, (∀ i, l ≤ μ i ∧ μ i ≤ U) →
        (∀ h : Extended F A →+* ℝ, Monotone h → (∀ T, h (Tensor.pad Unit T) = f T) →
          (∑ i, (radius g i / μ i) ^ 2) ≤ ∑ i, (radius h i / μ i) ^ 2) →
        ∃ e : A → ℕ, (∀ i, μ i * width (e i) / n ≤ radius g i / μ i + η) ∧
          ∑ i, (radius g i / μ i) ^ 2 ≤ price f z e / n + η ^ 2 + Fintype.card A * (1 / l) * η := by
  let D₀ := Fintype.card A * (1 / l) ^ 2
  have hD₀ : 0 ≤ D₀ := by unfold D₀; positivity
  let R := 4 * (D₀ + 1) / (l * entropy) ^ 2
  have hR : 0 < R := div_pos (by positivity) (sq_pos_of_pos (mul_pos hl entropy_pos))
  obtain ⟨C, ht⟩ := weighted_control (U := U) hE hW z hz hl hR
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((eventually_gt_atTop 0).and ht)
  filter_upwards [uniform_gap (I := A) D₀ (2 * (D₀ + 1)) C (by positivity) N (η ^ 2) (by positivity)]
    with n hn
  intro f hf g hg hgf μ hμ hvar
  let r i := radius g i / μ i
  let D := ∑ i, r i ^ 2
  have hp i := hl.trans_le (hμ i).1
  have hr (i : A) : 0 ≤ r i ∧ r i ≤ 1 / l :=
    ⟨div_nonneg (Tensor.dist_nonneg g hg _ _) (hp i).le,
      div_le_div₀ zero_le_one (Tensor.dist_le_one g hg _ _) hl (hμ i).1⟩
  have hD : D ≤ D₀ := by
    simpa [D, D₀] using sum_le_card_nsmul univ (fun i => r i ^ 2) ((1 / l) ^ 2)
      (fun i _ => pow_le_pow_left₀ (hr i).1 (hr i).2 2)
  have hprice : 0 ≤ price f z (fun _ => 0) := by
    unfold price
    generalize sphereTensor z (fun _ => 0) = T
    by_cases hT : T = 0
    · simp [hT]
    exact Real.log_nonneg (Tensor.value_one_le hf hT)
  have trans := transport_bound f g hg hgf z μ hp
  choose e he using Budget.maximizer trans hD hl (fun i => (hμ i).1) z hprice (cost_zero f z)
  let w (m : ℕ) i := μ i * width (e m i) / m
  let B (m : ℕ) := Budget.value (price f z) μ m (e m)
  have bound (m : ℕ) (hm : 0 < m) (i : A) :
      w m i ≤ 2 * (D₀ + 1) ∧ (e m i : ℝ) ≤ R * (m : ℝ) ^ 2 :=
    Budget.bounds trans hD hl (fun j => (hμ j).1) m hm (e m) (he m hm).1 i
  have hb : D < 2 * (B n / n) + η ^ 2 := by
    refine hn D w B hD (fun m hm => (he m (hN m hm).1).1) ?_ ?_ ?_
    · intro m hm i
      exact ⟨div_nonneg (mul_nonneg (hp i).le (width_nonneg _)) (by positivity),
        (bound m (hN m hm).1 i).1⟩
    · intro m hm
      obtain ⟨hpos, htest⟩ := hN m hm
      obtain ⟨_, hne, hmax⟩ := he m hpos
      obtain ⟨q, hq, hqf, hdist⟩ := htest f hf μ hμ (e m) hmax (fun i => (bound m hpos i).2) hne
      exact ⟨fun i => radius q i / μ i, fun i => div_nonneg (Tensor.dist_nonneg q hq _ _) (hp i).le,
        hvar q hq hqf, hdist⟩
    · intro m hm
      unfold w B
      rw [Budget.increment (p := price f z) _ _ (hN m hm).1]
      gcongr
      exact (he (m + 1) (by omega)).2.2 _
  have hs : 2 * (B n / n) + ∑ i, (w n i - r i) ^ 2 ≤ D := Budget.squares trans n (e n)
  have hi (i : A) : w n i ≤ r i + η ∧ r i ≤ w n i + η := by
    have := single_le_sum (fun j (_ : j ∈ univ) => sq_nonneg (w n j - r j)) (mem_univ i)
    constructor <;> nlinarith only [this, hs, hb, hη]
  refine ⟨e n, fun i => (hi i).1, ?_⟩
  have hi' (i : A) : r i ^ 2 ≤ w n i ^ 2 + 2 * (1 / l) * η := by
    nlinarith only [mul_le_mul_of_nonneg_left (hi i).2 (hr i).1,
      mul_le_mul_of_nonneg_right (hr i).2 hη.le, sq_nonneg (w n i - r i)]
  have hh := sum_le_sum (fun i (_ : i ∈ univ) => hi' i)
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at hh
  have heq : B n / n = price f z (e n) / n - (∑ i, w n i ^ 2) / 2 := Budget.normalize n (e n)
  change D ≤ _
  unfold D at hb ⊢
  linarith only [hh, heq, hb, sq_nonneg η]

/-- At all sufficiently large scales, every spectral point admits a
sphere within the prescribed caps whose log price approaches the
transport cost of the caps at a single extended site. -/
theorem prescribed_widths (hE : WeightedExtension F) (hW : WireProbe F)
    (z : A → F) (hz : Function.Injective z) (a : A → ℝ) (ha : ∀ i, 0 < a i)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ f : Tensor F A →+* ℝ, Monotone f →
      ∃ g : Tensor F (A ⊕ Unit) →+* ℝ, Monotone g ∧ (∀ T, g (Tensor.pad Unit T) = f T) ∧
        ∃ e : A → ℕ, (∀ i, width (e i) ≤ n * a i) ∧
          n * ((∑ i, a i * Tensor.dist g (.inl i) (.inr ())) - ε) ≤ Real.log (f (sphereTensor z e)) := by
  let S := ∑ i, a i
  have hS : 0 ≤ S := sum_nonneg fun i _ => (ha i).le
  let τ := min 1 (ε / 2 / (S + 1))
  have ht : 0 < τ := lt_min zero_lt_one (by positivity)
  have ht' : τ * S ≤ ε / 2 := by
    have := (le_div_iff₀ (by positivity : 0 < S + 1)).mp (show τ ≤ ε / 2 / (S + 1) from min_le_right _ _)
    linarith
  obtain ⟨l, U, hl, hU, weights⟩ := choose_weights (F := F) a ha ht (min_le_left _ _)
  let B := Fintype.card A * (1 / l)
  have hB : 0 ≤ B := by unfold B; positivity
  let η := min 1 (min (τ ^ 2 / 3 / U) (ε / 2 / (B + 1)))
  have hη : 0 < η := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hslack : η * U ≤ τ ^ 2 / 3 :=
    (le_div_iff₀ hU).mp ((min_le_right _ _).trans (min_le_left _ _))
  have herr : η ^ 2 + B * η ≤ ε / 2 := by
    have hm : η ≤ 1 := min_le_left _ _
    have hh : η * (B + 1) ≤ ε / 2 :=
      (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
    nlinarith
  filter_upwards [profile (U := U) hE hW z hz hl hη, eventually_gt_atTop 0] with n hp hn
  intro f hf
  obtain ⟨g, hg, he, μ, hμ, hs, hlow, hvar⟩ := weights f hf
  obtain ⟨e, hw, hc⟩ := hp f hf g hg he μ hμ hvar
  have hn' : 0 < (n : ℝ) := by positivity
  refine ⟨g, hg, he, e, fun i => ?_, ?_⟩
  · have hm := hl.trans_le (hμ i).1
    have hi := mul_le_mul_of_nonneg_right (hw i) hm.le
    rw [add_mul, div_mul_cancel₀ _ hm.ne'] at hi
    rw [mul_comm, ← div_le_iff₀ hn']
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hm)).mp
    calc
      _ = μ i * width (e i) / n * μ i := by ring
      _ ≤ radius g i + η * μ i := hi
      _ ≤ radius g i + τ ^ 2 / 3 :=
        add_le_add_right ((mul_le_mul_of_nonneg_left (hμ i).2 hη.le).trans hslack) _
      _ ≤ _ := hs i
  · rw [mul_comm, ← le_div_iff₀ hn']
    change (∑ i, a i * radius g i) - ε ≤ price f z e / n
    unfold S at ht'
    unfold B at herr
    linarith only [hc, hlow, ht', herr]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! Simultaneous price bounds for one moving sphere insertion. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral Sphere Finset Polynomial
open scoped Classical

variable {A F : Type} [Field F] [Fintype A]

private theorem regular_denominator (a : A → Fin 2 → F) (s : F)
    (h : Function.Injective (fun i => position (a i) s 1)) :
    denominator (directions a) s 1 ≠ 0 := by
  refine prod_ne_zero_iff.mpr fun d hd => ?_
  rcases mem_insert.mp hd with hnone | hm
  · simp [linearFactor, hnone]
  obtain ⟨_, hk, rfl⟩ := mem_image.mp hm
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := mem_image.mp hk
  have hi := through_left (a i) (a j)
  have hj := through_right (a i) (a j)
  generalize through (a i) (a j) = k at *
  obtain ⟨_ | d, t⟩ := k
  · exact one_ne_zero
  intro he
  have hs : s = -d := by simpa [linearFactor, add_eq_zero_iff_eq_neg] using he
  apply (mem_filter.mp hij).2
  apply h
  simpa [projection, position, hs, sub_eq_add_neg, add_comm, mul_comm] using hi.trans hj.symm

variable [Nonempty A]

private theorem scalar_le (X : A → Type) [∀ i, Fintype (X i)]
    (T U : (∀ i, X i) → F) (c : F) (h : ∀ v, T v = c * U v) :
    Tensor.ofRaw (Raw.ofTable X T) ≤ Tensor.ofRaw (Raw.ofTable X U) := by
  simpa using Tensor.span_le X T (fun _ : Unit => U) (fun _ => c) (by simp [h])

omit [Nonempty A] in
private theorem movingFamily (z : A → F) (hz : Function.Injective z) (e : A ⊕ Unit → ℕ) :
    ∃ p : States 1 e → F[X], ∀ s ∉ Set.range z,
      Prices.evalFamily (fun i => Level 1 (e i)) p s = sphereTensor (Sum.elim z (fun _ => s)) e := by
  let a : A ⊕ Unit → Fin 2 → F := Sum.elim (fun i => ![0, z i]) (fun _ => ![1, 0])
  refine ⟨fun v => correlatorPoly a (X : F[X]) 1 (inputs v), fun s hs => ?_⟩
  let t := Sum.elim z (fun _ : Unit => s)
  have he (i) : position (a i) s 1 = t i := by cases i <;> simp [a, position, t]
  have hi : Function.Injective t := by
    rintro (i|⟨⟩) (j|⟨⟩) h
    · exact congrArg Sum.inl (hz h)
    · exact (hs ⟨i, h⟩).elim
    · exact (hs ⟨j, h.symm⟩).elim
    · rfl
  have hd := regular_denominator a s (by simpa only [he] using hi)
  let c := denominator (directions a) s 1 ^ ((∑ i, e i) / 2)
  have hc : c ≠ 0 := pow_ne_zero _ hd
  have eqn (v : States 1 e) :
      (correlatorPoly a (X : F[X]) 1 (inputs v)).eval s = c * sphereForm t e v := by
    have h := correlator_map (aeval s) a (X : F[X]) 1 (inputs v)
    simp only [aeval_X, map_one, correlator_specialize _ _ _ hd, he, weight_inputs] at h
    simpa [c, sphereForm] using h
  refine le_antisymm (scalar_le _ _ _ c eqn) (scalar_le _ _ _ c⁻¹ fun v => ?_)
  change sphereForm t e v = c⁻¹ * (correlatorPoly a (X : F[X]) 1 (inputs v)).eval s
  rw [eqn, inv_mul_cancel_left₀ hc]

theorem BoundedForms.weighted (h : BoundedForms F) (sync : Prices.SharedPrice F) :
    WeightedExtension F := by
  intro A _ _ _ f hf z hz B t ht he M
  let I := {e : A ⊕ Unit → ℕ // ∀ i, e i ≤ M}
  let X (e : I) (i) := Level 1 (e.1 i)
  let p (e : I) := ((M : ℝ) + 2) ^ (Fintype.card A + 8) * Real.exp (B + ∑ i, t i * (e.1 i : ℝ))
  choose P hP using fun i : I => movingFamily z hz i.1
  obtain ⟨g, hg, hext, hbound⟩ := sync A I f hf (univ.image z) X P p (by
    intro s hs w T hT
    have hs' : s ∉ Set.range z := by simpa using hs
    have hh := h A f hf z hz B t ht he s hs' M
      (w.map Subtype.val) (by
        intro e he
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
        exact v.2) T
    simp only [List.map_map, Function.comp_def] at hh
    apply hh
    simpa only [X, hP _ s hs'] using hT)
  refine ⟨g, hg, hext, fun s hs e he => ?_⟩
  have eq := hP ⟨e, he⟩ s hs
  change Prices.evalFamily (X ⟨e, he⟩) (P ⟨e, he⟩) s = sphereTensor _ e at eq
  rw [← eq]
  exact hbound ⟨e, he⟩ s (by simpa using hs)

theorem BoundedForms.extension (h : BoundedForms F) (sync : Prices.SharedPrice F) :
    BoundedExtension F := (h.weighted sync).uniform

end OAI.LinearAlgebra.MatrixExponent.Routing
end
