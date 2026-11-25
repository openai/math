import OAI.Computability.BorderVNP.PackedHistoryOuter

/-! # Gate and guess budget for the compiled full Boolean history

Both the frame and its actual static input type are charged. The bound remains
uniform in the team count, in the computed leaf frames, and in the state
and profile bank formats at each height.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Filter Packing Shortening.Adaptive TeamScales VPVNP.VerifierNetwork

/-- Eventual strict cost bound on the actual compiled frame and its static profile pins. -/
def CompiledBudget (k b D Q : ℕ) (α τ growth γ : ℝ) : Prop :=
    ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℝ, 0 ≤ A →
      ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n : ℝ)^ω) →
      let T := epochs τ n
      let cap := A * (r * (n : ℝ)^(9/10 : ℝ)) * (growth^T * width n α) * (logWidth r n : ℝ)^D
      ∀ (σ : Type) [Fintype σ] (W G : ℕ → Type) [∀ j, Fintype (W j)] [∀ j, Fintype (G j)]
        (step : Steps k (b*T) W G) (fs : Leaves k (Frame σ (W 0)) (b*T)) (L M U : ℕ),
        ((L+1 : ℕ) : ℝ) ≤ cap → (M : ℝ) ≤ cap → (U : ℝ) ≤ cap →
        everyLeaf (fun f : Frame σ (W 0) => f.size ≤ L) (b*T) fs →
        (∀ j (hj : j<b*T), (step j hj).size + (2*k+4) ≤ M) →
        (∀ j < b*T, Fintype.card (G j) ≤ U) →
        ((Q*(compile step (b*T) le_rfl fs).size + Fintype.card (Slot k G (b*T)) : ℕ) : ℝ) <
          r * (n : ℝ)^γ

/-- Any strictly larger exponent than the sparse resource exponent absorbs a fixed gate
serialization factor and the entire profile-word bank. -/
theorem eventually_compiled_history_below {α τ growth : ℝ} {k : ℕ} (b D Q : ℕ)
    (hα : α < 1/1000) (hτ : 0 < τ) (hτ' : τ < α/100) (hk : 0 < k)
    (hteams : τ * Real.logb 2 (k^b : ℕ) ≤ α) (hg : 1 ≤ growth)
    (hgrowth : τ * Real.logb 2 growth ≤ α/10) (γ : ℝ)
    (hγ : 2*α+9/10+1/100+τ/2000 < γ) : CompiledBudget k b D Q α τ growth γ := by
  let β := (2*α+9/10+1/100+τ/2000+γ)/2
  have hβ : 2*α+9/10+1/100+τ/2000 < β := by dsimp [β]; linarith
  have hβγ : β < γ := by dsimp [β]; linarith
  obtain ⟨ω,hω,work⟩ := eventually_historyTreeCost_below b D hα hτ hτ' hk hteams hg hgrowth β hβ
  refine ⟨ω,hω,fun A hA => ?_⟩
  filter_upwards [work A hA, eventually_rpow_gap hβγ (Q+1)] with n htree hgap
  intro r hr hmax T cap σ _ W G _ _ step fs L M U hL hM hU hf hm hu
  have hs := compile_size step (b*T) le_rfl fs L M hf hm
  have hc := slot_card_le k G (b*T) U hu
  have hx : ((compile step (b*T) le_rfl fs).size : ℝ) < r*(n:ℝ)^β :=
    (by exact_mod_cast hs : ((compile step (b*T) le_rfl fs).size : ℝ) ≤ historyTreeCost k (L+1) M (b*T)).trans_lt
      (htree r hr hmax (L+1) M hL hM)
  have hy : (Fintype.card (Slot k G (b*T)) : ℝ) < r*(n:ℝ)^β :=
    (by exact_mod_cast hc : (Fintype.card (Slot k G (b*T)) : ℝ) ≤ historyTreeCost k 0 U (b*T)).trans_lt
      (htree r hr hmax 0 U (by simpa using (Nat.cast_nonneg (L+1)).trans hL) hU)
  push_cast
  calc
    _ < (Q:ℝ)*(r*(n:ℝ)^β) + r*(n:ℝ)^β :=
      add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx.le (Nat.cast_nonneg _)) hy
    _ = r*((Q+1)*(n:ℝ)^β) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg _)

/-- The public frame and all guessed count bits fit below exponent 0.92, leaving room for the native traversal in Proposition 7.2(ii). -/
theorem eventually_compiled_history_92 {α τ growth : ℝ} {k : ℕ} (b D Q : ℕ)
    (hα : α < 1/1000) (hτ : 0 < τ) (hτ' : τ < α/100) (hk : 0 < k)
    (hteams : τ * Real.logb 2 (k^b : ℕ) ≤ α) (hg : 1 ≤ growth)
    (hgrowth : τ * Real.logb 2 growth ≤ α/10) : CompiledBudget k b D Q α τ growth (92/100) :=
  eventually_compiled_history_below b D Q hα hτ hτ' hk hteams hg hgrowth _ (by linarith)

/-- The compiled history also fits the block scheduler allowance at exponent 0.95. -/
theorem eventually_compiled_history {α τ growth : ℝ} {k : ℕ} (b D Q : ℕ)
    (hα : α < 1/1000) (hτ : 0 < τ) (hτ' : τ < α/100) (hk : 0 < k)
    (hteams : τ * Real.logb 2 (k^b : ℕ) ≤ α) (hg : 1 ≤ growth)
    (hgrowth : τ * Real.logb 2 growth ≤ α/10) : CompiledBudget k b D Q α τ growth (95/100) :=
  eventually_compiled_history_below b D Q hα hτ hτ' hk hteams hg hgrowth _ (by linarith)

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
