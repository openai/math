import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

variable {V : Type*}

/-- Weight of an ordered tuple of independent draws from the vertex distribution. -/
def drawWeight {n : ℕ} (p : V → ℚ) (x : Fin n → V) : ℚ :=
  ∏ j, p (x j)

theorem drawWeight_nonneg {n : ℕ} {p : V → ℚ} (hp : ∀ v, 0 ≤ p v) (x : Fin n → V) :
    0 ≤ drawWeight p x :=
  Finset.prod_nonneg fun j _ => hp (x j)

variable [Fintype V]

theorem sum_drawWeight {n : ℕ} {p : V → ℚ} (hp : ∑ v, p v = 1) :
    ∑ x : Fin n → V, drawWeight p x = 1 := by
  simpa [drawWeight, hp] using
    (Fintype.prod_sum (κ := fun _ : Fin n => V) (fun _ v => p v)).symm

section

variable [DecidableEq V]

/-- Tuples with no member of the specified set in any coordinate. -/
def missTuples (n : ℕ) (good : Finset V) : Finset (Fin n → V) :=
  Fintype.piFinset fun _ => goodᶜ

theorem mem_missTuples {n : ℕ} (good : Finset V) (x : Fin n → V) :
    x ∈ missTuples n good ↔ ∀ j, x j ∉ good := by
  simp [missTuples, Fintype.mem_piFinset]

theorem mem_hitTuples {n : ℕ} (good : Finset V) (x : Fin n → V) :
    x ∈ (missTuples n good)ᶜ ↔ ∃ j, x j ∈ good := by
  classical
  simp [mem_missTuples]

theorem tuple_miss_mass {p : V → ℚ} (hp : ∑ v, p v = 1) (good : Finset V) (n : ℕ) :
    ∑ x ∈ missTuples n good, drawWeight p x = (1 - ∑ v ∈ good, p v) ^ n := by
  have hm := Finset.sum_add_sum_compl good p
  rw [hp] at hm
  have hc : ∑ v ∈ goodᶜ, p v = 1 - ∑ v ∈ good, p v := by linarith
  simpa only [drawWeight, missTuples, ← hc] using (Finset.sum_pow' goodᶜ p n).symm

theorem tuple_hit_mass {p : V → ℚ} (hp : ∑ v, p v = 1) (good : Finset V) (n : ℕ) :
    ∑ x ∈ (missTuples n good)ᶜ, drawWeight p x = 1 - (1 - ∑ v ∈ good, p v) ^ n := by
  have hm := Finset.sum_add_sum_compl (missTuples n good) (drawWeight p)
  rw [sum_drawWeight hp, tuple_miss_mass hp] at hm
  linarith

/-- Expected probe gain when a hit pays at least one and all missed tuples pay at least b. -/
theorem expected_gain_of_hit {n : ℕ} (p : V → ℚ) (hp₀ : ∀ v, 0 ≤ p v)
    (hp : ∑ v, p v = 1) (good : Finset V) (gain : (Fin n → V) → ℚ) (b : ℚ)
    (hit : ∀ x, (∃ j, x j ∈ good) → 1 ≤ gain x)
    (miss : ∀ x, (∀ j, x j ∉ good) → b ≤ gain x) :
    1 - (1 - b) * (1 - ∑ v ∈ good, p v) ^ n ≤
      ∑ x, drawWeight p x * gain x := by
  classical
  let S := missTuples n good
  have hb : ∑ x ∈ S, drawWeight p x * b ≤ ∑ x ∈ S, drawWeight p x * gain x :=
    Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left
      (miss x ((mem_missTuples good x).mp hx)) (drawWeight_nonneg hp₀ x)
  have ht : ∑ x ∈ Sᶜ, drawWeight p x ≤ ∑ x ∈ Sᶜ, drawWeight p x * gain x := by
    apply Finset.sum_le_sum
    intro x hx
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (hit x ((mem_hitTuples good x).mp hx)) (drawWeight_nonneg hp₀ x)
  have hsum := add_le_add hb ht
  rw [← Finset.sum_mul, Finset.sum_add_sum_compl] at hsum
  change (∑ x ∈ missTuples n good, drawWeight p x) * b +
      (∑ x ∈ (missTuples n good)ᶜ, drawWeight p x) ≤ _ at hsum
  rw [tuple_miss_mass hp, tuple_hit_mass hp] at hsum
  linarith

/-- In the high-surplus case the top band has probability at least δ/2 = 1/32. -/
theorem high_surplus_expected_gain (p : V → ℚ) (hp₀ : ∀ v, 0 ≤ p v)
    (hp : ∑ v, p v = 1) (good : Finset V) (mass : 1 / 32 ≤ ∑ v ∈ good, p v)
    (gain : (Fin 64 → V) → ℚ) (hit : ∀ x, (∃ j, x j ∈ good) → 1 ≤ gain x)
    (lb : ∀ x, -1 ≤ gain x) : 1 / 2 ≤ ∑ x, drawWeight p x * gain x := by
  have hc := Finset.sum_add_sum_compl good p
  rw [hp] at hc
  have h₀ : 0 ≤ 1 - ∑ v ∈ good, p v := by
    have hn : 0 ≤ ∑ v ∈ goodᶜ, p v := Finset.sum_nonneg fun v _ => hp₀ v
    linarith
  have hw : 1 - ∑ v ∈ good, p v ≤ 31 / 32 := by linarith
  have hd := pow_le_pow_left₀ h₀ hw 64
  have he := expected_gain_of_hit p hp₀ hp good gain (-1) hit (fun x _ => lb x)
  have h64 : (31 / 32 : ℚ) ^ 64 ≤ 1 / 4 := by norm_num
  linarith

/-- A low-surplus passing probe never loses; all tuples with a positive-surplus draw win. -/
theorem low_surplus_expected_gain (k : ℕ) (p : V → ℚ) (hp₀ : ∀ v, 0 ≤ p v)
    (hp : ∑ v, p v = 1) (good : Finset V) (gain : (Fin (k + 1) → V) → ℚ)
    (hit : ∀ x, (∃ j, x j ∈ good) → 1 ≤ gain x) (lb : ∀ x, 0 ≤ gain x) :
    ∑ v ∈ good, p v ≤ ∑ x, drawWeight p x * gain x := by
  have hc := Finset.sum_add_sum_compl good p
  rw [hp] at hc
  have hg : 0 ≤ ∑ v ∈ good, p v := Finset.sum_nonneg fun v _ => hp₀ v
  have hm : 0 ≤ ∑ v ∈ goodᶜ, p v := Finset.sum_nonneg fun v _ => hp₀ v
  have h₀ : 0 ≤ 1 - ∑ v ∈ good, p v := by linarith
  have h₁ : 1 - ∑ v ∈ good, p v ≤ 1 := by linarith
  have hw := pow_le_one₀ h₀ h₁ (n := k)
  have hz := mul_le_mul_of_nonneg_right hw h₀
  have he := expected_gain_of_hit p hp₀ hp good gain 0 hit (fun x _ => lb x)
  rw [pow_succ] at he
  linarith

end

/-- With positive total active mass, normalizing gives the distribution used in every probe. -/
theorem active_distribution {m : V → ℚ} (hm : ∀ v, 0 ≤ m v) (hM : 0 < ∑ v, m v) :
    (∀ v, 0 ≤ m v / ∑ i, m i) ∧ ∑ v, (m v / ∑ i, m i) = 1 := by
  constructor
  · exact fun v => div_nonneg (hm v) hM.le
  · rw [← Finset.sum_div, div_self hM.ne']

/-- Normalizing active mass at most one increases the probability of each subset. -/
theorem active_subset_mass {m : V → ℚ} (hm : ∀ v, 0 ≤ m v) (hM : 0 < ∑ v, m v)
    (hM₁ : ∑ v, m v ≤ 1) (good : Finset V) :
    ∑ v ∈ good, m v ≤ ∑ v ∈ good, m v / ∑ i, m i := by
  rw [← Finset.sum_div, le_div_iff₀ hM]
  have h := mul_le_mul_of_nonneg_left hM₁
    (Finset.sum_nonneg (s := good) (fun v _ => hm v))
  simpa only [mul_one] using h

/-- A positive-surplus hit excludes the outside option. All allocated goods then
dominate the hit, so equality of their feedback signs makes the gain one. -/
theorem gain_eq_one_of_pivot_hit {n : ℕ} (x : Fin n → V) (surplus label f : V → ℚ)
    (out pivot : ℚ) (f₀ : ∀ i, 0 ≤ f i) (out₀ : 0 ≤ out)
    (mass : (∑ i, f i) + out = 1)
    (outMax : 0 < out → ∀ j, surplus (x j) ≤ 0)
    (maximal : ∀ i, 0 < f i → ∀ j, surplus (x j) ≤ surplus i)
    (correct : ∀ i, 0 < f i → pivot ≤ surplus i → label i = 1)
    (hit : ∃ j, pivot ≤ surplus (x j) ∧ 0 < surplus (x j)) :
    ∑ i, f i * label i = 1 := by
  obtain ⟨j, hj, hpos⟩ := hit
  have ho : out = 0 := le_antisymm (le_of_not_gt (fun h => hpos.not_ge (outMax h j))) out₀
  calc
    ∑ i, f i * label i = ∑ i, f i := by
      apply Finset.sum_congr rfl
      intro i _
      rcases (f₀ i).eq_or_lt with h | h
      · simp [← h]
      · rw [correct i h (hj.trans (maximal i h j)), mul_one]
    _ = 1 := by simpa [ho] using mass

/-- If all eligible maximizing goods have correct feedback, the gain is nonnegative
even when the zero-surplus outside option receives positive mass. -/
theorem gain_nonneg_of_correct_maxima (surplus label f : V → ℚ) (f₀ : ∀ i, 0 ≤ f i)
    (beatsOutside : ∀ i, 0 < f i → 0 ≤ surplus i)
    (correct : ∀ i, 0 < f i → 0 ≤ surplus i → label i = 1) :
    0 ≤ ∑ i, f i * label i := by
  apply Finset.sum_nonneg
  intro i _
  rcases (f₀ i).eq_or_lt with h | h
  · simp [← h]
  · simpa [correct i h (beatsOutside i h)] using h.le

/-- Even without feedback guarantees, a subprobability allocation with signs in [-1,1]
has gain at least -1. -/
theorem gain_ge_neg_one (label f : V → ℚ) (f₀ : ∀ i, 0 ≤ f i)
    (mass : ∑ i, f i ≤ 1) (sign : ∀ i, -1 ≤ label i) :
    -1 ≤ ∑ i, f i * label i := by
  have h : ∑ i, f i * (-1) ≤ ∑ i, f i * label i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (sign i) (f₀ i)
  rw [← Finset.sum_mul] at h
  linarith

/-- Local expert allocations give mass only to the goods maximizing the tuple surplus and the
outside option, whose surplus is zero. The goods in a tuple may repeat. -/
structure ProbeAllocation (n : ℕ) (surplus : V → ℚ) where
  weight : (Fin n → V) → V → ℚ
  outside : (Fin n → V) → ℚ
  nonneg : ∀ x i, 0 ≤ weight x i
  outside_nonneg : ∀ x, 0 ≤ outside x
  total : ∀ x, (∑ i, weight x i) + outside x = 1
  supported : ∀ x i, 0 < weight x i → ∃ j, x j = i
  outside_max : ∀ x, 0 < outside x → ∀ j, surplus (x j) ≤ 0
  inside_max : ∀ x i, 0 < weight x i → ∀ j, surplus (x j) ≤ surplus i
  beats_outside : ∀ x i, 0 < weight x i → 0 ≤ surplus i

/-- The local-expert estimate for either kind of passing probe. The high-surplus branch
uses the common top band of the quantile construction; its raw mass is at least 1/32.
The labels are multiplied by the hidden sign, so correct feedback is represented by one. -/
theorem passing_probe_expected_gain [DecidableEq V] (m surplus label : V → ℚ)
    (A : ProbeAllocation 64 surplus) (hm : ∀ i, 0 ≤ m i) (hm₀ : 0 < ∑ i, m i)
    (hm₁ : ∑ i, m i ≤ 1) (hsign : ∀ i, -1 ≤ label i)
    (pos : Finset V) (hpos : ∀ i, i ∈ pos ↔ 0 < surplus i)
    (low : (∑ i ∈ pos, m i) ≤ 1 / 16 → ∀ i, 0 ≤ surplus i → label i = 1)
    (high : 1 / 16 < ∑ i ∈ pos, m i → ∃ (band : Finset V) (pivot : ℚ),
      1 / 32 ≤ ∑ i ∈ band, m i ∧
      (∀ i ∈ band, pivot ≤ surplus i ∧ 0 < surplus i) ∧
      (∀ i, pivot ≤ surplus i → label i = 1)) :
    (∑ i ∈ pos, m i) / 2 ≤
      ∑ x : Fin 64 → V, drawWeight (fun i => m i / ∑ j, m j) x *
        ∑ i, A.weight x i * label i := by
  let p (i : V) := m i / ∑ j, m j
  let gain (x : Fin 64 → V) := ∑ i, A.weight x i * label i
  have ⟨hp₀, hp⟩ := active_distribution hm hm₀
  have hraw : ∑ i ∈ pos, m i ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ pos)
      (fun i _ _ => hm i)).trans hm₁
  by_cases hlo : (∑ i ∈ pos, m i) ≤ 1 / 16
  · have hl := low hlo
    have uniform : ∀ x, 0 ≤ gain x := fun x =>
      gain_nonneg_of_correct_maxima surplus label (A.weight x) (A.nonneg x)
        (A.beats_outside x) (fun i _ hs => hl i hs)
    have wins : ∀ x : Fin 64 → V, (∃ j, x j ∈ pos) → 1 ≤ gain x := by
      rintro x ⟨j, hj⟩
      have hpos' := (hpos (x j)).mp hj
      exact (gain_eq_one_of_pivot_hit x surplus label (A.weight x) (A.outside x) 0
        (A.nonneg x) (A.outside_nonneg x) (A.total x) (A.outside_max x)
        (A.inside_max x) (fun i _ h => hl i h) ⟨j, hpos'.le, hpos'⟩).ge
    have bound := low_surplus_expected_gain 63 p hp₀ hp pos gain wins uniform
    have half : (∑ i ∈ pos, m i) / 2 ≤ ∑ i ∈ pos, m i := by
      have hn := Finset.sum_nonneg (s := pos) (fun i _ => hm i)
      linarith
    exact (half.trans (active_subset_mass hm hm₀ hm₁ pos)).trans bound
  · obtain ⟨band, pivot, hband, hhit, hlabel⟩ := high (lt_of_not_ge hlo)
    have wins : ∀ x : Fin 64 → V, (∃ j, x j ∈ band) → 1 ≤ gain x := by
      rintro x ⟨j, hj⟩
      exact (gain_eq_one_of_pivot_hit x surplus label (A.weight x) (A.outside x) pivot
        (A.nonneg x) (A.outside_nonneg x) (A.total x) (A.outside_max x)
        (A.inside_max x) (fun i _ h => hlabel i h) ⟨j, hhit (x j) hj⟩).ge
    have uniform : ∀ x, -1 ≤ gain x := by
      intro x
      apply gain_ge_neg_one label (A.weight x) (A.nonneg x) _ hsign
      linarith [A.total x, A.outside_nonneg x]
    have bound := high_surplus_expected_gain p hp₀ hp band
      (hband.trans (active_subset_mass hm hm₀ hm₁ band)) gain wins uniform
    change (∑ i ∈ pos, m i) / 2 ≤ ∑ x, drawWeight p x * gain x
    exact (by linarith : (∑ i ∈ pos, m i) / 2 ≤ 1 / 2).trans bound

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
