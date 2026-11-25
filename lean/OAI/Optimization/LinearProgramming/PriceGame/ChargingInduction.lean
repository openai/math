import OAI.Optimization.LinearProgramming.PriceGame.ChargingProbe

/-! # Charging under induction on the height of the trial tree

For a probe, use the common adaptive threshold distribution given by its
`ProbeTest`. On the final calls only the inherited transition is needed, and only
when the median baseline has small violating mass. All scores at a call are
shared across its hypotheses about the hidden state.
-/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

open Finset

/-- A deterministic choice of the inherited shift. -/
def inheritDensity {V : Type*} (j : Option V) : ℚ := j.elim 1 (fun _ => 0)

/-- The group charge using the child induction hypothesis for each tested
state. The `transfer` premise is the pointwise one-step transfer of Lemma 6.1;
it uses only distributions on admissible pivots, with the cap `32mᵢ`.
The means, ceilings, and the probe/final call split are computed here. -/
theorem trial_charge_of_child_states {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V]
    {k : ℕ} (h : Bool) (m t : V → ℚ) (probe out : Calls k → V → ℚ)
    (surplus : Sum (Calls k) (Calls k) → V → ℚ) (label : Calls k → V → ℚ)
    (alloc : ∀ b, ProbeAllocation 64 (surplus (.inl b)))
    (success : Sum (Calls k) (Calls k) → Option V → Prop)
    (w : F → ℚ) (wc : Sum (Calls k) (Calls k) → Option V → F → ℚ)
    (s : Sum (Calls k) (Calls k) → F → ℚ)
    (hm : ∀ i, 0 ≤ m i) (hM : ∑ i, m i ≤ 1) (hMpos : 0 < ∑ i, m i)
    (hw : ∀ e, 0 ≤ w e) (hwSum : ∑ e, w e ≤ 1) (hs : ∀ b e, 0 ≤ s b e)
    (hl : ∀ b i, -1 ≤ label b i)
    (hpMass : ∀ b, positiveMass m (surplus (.inl b)) = violatedMass m h t (probe b))
    (hfMass : ∀ b, positiveMass m (surplus (.inr b)) =
      violatedMass m h t (fun i => oddMedian fun a => probe a i))
    (tested : ∀ b, Nonempty (ProbeTest m (surplus (.inl b)) (success (.inl b))
      (weighted (tupleDistribution m) (probeGain (alloc b) (label b)))))
    (returned : ∃ i, misses h (t i) (oddMedian fun b => out b i) = true)
    (inheritPass : ∀ b, success (.inr b) none → ∀ i, misses h (t i) (out b i) = false)
    (transfer : ∀ b (μ : Option V → ℚ), (∀ o, 0 ≤ μ o) → (∑ o, μ o) = 1 →
      (∀ i, μ (some i) ≤ 32 * m i) → (∀ o, 0 < μ o → admissibleTest m (surplus b) o) →
      ∀ e, weighted μ (fun o => wc b o e) ≤ (8/(1/16 : ℚ)^65) * w e)
    (childIH : ∀ b o, admissibleTest m (surplus b) o → ¬ success b o → 1 ≤ weighted (wc b o) (s b)) :
    let σ := (1/16 : ℚ) / (32 * (8/(1/16 : ℚ)^65))
    1 ≤ weighted (fun x => (∑ i, m i)^64/4 * tupleDistribution m x)
        (fun x => (roundCharge σ (weighted (uniform k) (fun b => probeGain (alloc b) (label b) x)) : ℚ)) +
      weighted w (fun e => (roundCharge σ (weighted (childWeights (uniform k)) (fun b => s b e)) : ℚ)) := by
  classical
  let T b := Classical.choice (tested b)
  let med := violatedMass m h t (fun i => oddMedian fun b => probe b i)
  let ff (b : Calls k) := decide (med ≤ (1/16 : ℚ) ∧ ¬success (.inr b) none)
  let mu : Sum (Calls k) (Calls k) → Option V → ℚ := Sum.elim (fun b => (T b).density) (fun _ => inheritDensity)
  let failed := Sum.elim (fun b => (T b).failed) ff
  have hμ (b) : ∀ o, 0 ≤ mu b o := by
    cases b with
    | inl b => exact (T b).nonneg
    | inr b => rintro (_|i) <;> norm_num [mu, inheritDensity]
  have hμsum (b) : (∑ o, mu b o) = 1 := by
    cases b with
    | inl b => exact (T b).normalized
    | inr b => simp [mu, inheritDensity, Fintype.sum_option]
  have hμcap (b) (i : V) : mu b (some i) ≤ 32*m i := by
    cases b with
    | inl b => exact (T b).cap i
    | inr b => simpa [mu, inheritDensity] using (hm i)
  have eligible (b) (hb : failed b = true) (o : Option V) (ho : 0 < mu b o) :
      admissibleTest m (surplus b) o ∧ ¬success b o := by
    cases b with
    | inl b => exact ⟨(T b).allowed o ho, (T b).all_fail hb o ho⟩
    | inr b =>
      have hn : med ≤ (1/16 : ℚ) ∧ ¬success (.inr b) none := by simpa [failed, ff] using hb
      cases o with
      | none => exact ⟨(hfMass b).trans_le hn.1, hn.2⟩
      | some i => simp [mu, inheritDensity] at ho
  let q := tupleDistribution m
  obtain ⟨hp0, hp1⟩ := active_distribution hm hMpos
  have hq (x : Fin 64 → V) : 0 ≤ q x := drawWeight_nonneg hp0 x
  have hqsum : ∑ x, q x = 1 := sum_drawWeight hp1
  have hloc : ∑ x, (∑ i, m i)^64/4*q x ≤ 1 := by
    rw [← mul_sum, hqsum, mul_one]
    have hp := pow_le_one₀ hMpos.le hM (n := 64)
    linarith
  apply failed_price_trial 64 (1/16) (by norm_num) (by norm_num) h m t probe out q w
    (fun b => probeGain (alloc b) (label b)) (fun b e => weighted (mu b) (fun o => wc b o e)) s
    (fun b => (T b).failed) ff hm hM hq hw hloc hwSum returned _ _ _ hs _ _
  · intro hsmall b hb
    have hwin : success (.inr b) none := by
      by_contra hn
      have hf : ff b = true := decide_eq_true ⟨hsmall, hn⟩
      simp [hf] at hb
    exact inheritPass b hwin
  · intro b hb
    rw [← hpMass b]
    exact (T b).pass_gain hb
  · exact fun b _ => probeGain_lower (alloc b) hm hMpos (hl b)
  · intro b hb
    exact transfer b (mu b) (hμ b) (hμsum b) (hμcap b) (fun o ho => (eligible b hb o ho).1)
  · intro b hb
    apply charge_mixture (mu b) (wc b) (s b) (hμ b) (hμsum b)
    exact fun o ho => childIH b o (eligible b hb o ho).1 (eligible b hb o ho).2

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
