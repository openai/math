import OAI.Computability.BorderVNP.PackedHistoryAdapters
import OAI.Computability.BorderVNP.PackedHistoryBudget

/-! # Uniform cost of the actual nested epoch DAG, including both boundary frames -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Filter Packing Shortening.Adaptive TeamScales VPVNP.VerifierNetwork

variable {k b T : ℕ} {O : ℕ → Type} {W G : ℕ → ℕ → Type}
    [∀ t, Fintype (O t)] [∀ t j, Fintype (W t j)] [∀ t j, Fintype (G t j)]
    (inner : ∀ t, t<T → Steps k b (W t) (G t))
    (pre : ∀ t, t<T → Frame (Fin (k^b) × O t) (Fin (k^b) × W t 0))
    (post : ∀ t, t<T → Frame ((Fin (k^b) × O t) ⊕ W t b) (O (t+1)))

/-- The same outer tree consumes genuine subdivisions, all inner count fields,
and the returned rounded site bank at each successive epoch. -/
noncomputable def nestedSteps : Steps (k^b) T O (fun t => Slot k (G t) b) :=
  fun t ht => wrappedEpoch (pre t ht) (inner t ht) (post t ht)

/-- The fixed inner depth and fixed fan-in multiply the per-node cap by this
constant; the surrounding subdivision and rounding are each charged once. -/
def epochFactor (k b : ℕ) : ℕ := 2 + (k^b)*(1+b) + 2*(k^b)+4

theorem nestedSteps_size (hk : 0<k) (M : ℕ) (hM : 1≤M) (t : ℕ) (ht : t<T)
    (start : (pre t ht).size ≤ M) (finish : (post t ht).size ≤ M)
    (nodes : ∀ j (hj : j<b), (inner t ht j hj).size + (2*k+4) ≤ M) :
    (nestedSteps inner pre post t ht).size + (2*(k^b)+4) ≤ epochFactor k b*M := by
  have htree := (flatEpoch_size (inner t ht) M nodes).trans (historyTreeCost_le hk 1 M b)
  have hinner : (flatEpoch (inner t ht)).size ≤ (k^b)*((1+b)*M) :=
    htree.trans (Nat.mul_le_mul_left _ (by rw [Nat.add_mul,one_mul]; omega))
  have overhead : 2*(k^b)+4 ≤ (2*(k^b)+4)*M := Nat.le_mul_of_pos_right _ hM
  change (wrappedEpoch (pre t ht) (inner t ht) (post t ht)).size + _ ≤ _
  rw [wrappedEpoch_size]
  calc
    _ ≤ M + (k^b)*((1+b)*M) + M + (2*(k^b)+4)*M :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add start hinner) finish) overhead
    _ = _ := by unfold epochFactor; ring

/-- The outer node's true guess type is the disjoint union of its inner guesses,
with no rank, motion ordinal, padding or duplicate witnesses added by nesting. -/
theorem nestedSlots_size (k b M : ℕ) (hk : 0<k) (G : ℕ → Type) [∀ j, Fintype (G j)]
    (fields : ∀ j<b, Fintype.card (G j) ≤ M) : Fintype.card (Slot k G b) ≤ epochFactor k b*M := by
  have h := (slot_card_le k G b M fields).trans (historyTreeCost_le hk 0 M b)
  refine h.trans ?_
  unfold epochFactor
  ring_nf
  omega

private theorem repeated_size {σ U : Type} [Fintype σ] [Fintype U] (k : ℕ) (f : Frame σ U) (n : ℕ) :
    everyLeaf (fun g : Frame σ U => g.size ≤ f.size) n (repeatLeaf k f n) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact fun _ => ih

set_option maxHeartbeats 1200000 in
/-- Both kinds of public work on the actual epoch circuit fit the strict 0.92
exponent. The bound is uniform over the physical circuits for every absolute
level and over the number of processors in the specified range. -/
theorem eventually_nested_history_92 {α τ growth : ℝ} {k : ℕ} (b D Q : ℕ)
    (hα : α < 1/1000) (hτ : 0<τ) (hτ' : τ < α/100) (hk : 0<k)
    (hteams : τ*Real.logb 2 (k^b : ℕ) ≤ α) (hg : 1≤growth) (hgrowth : τ*Real.logb 2 growth ≤ α/10) :
    ∃ ω : ℝ, 0<ω ∧ ∀ A : ℝ, 0≤A → ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ) ≤ 2^((n:ℝ)^ω) →
      let T := epochs τ n
      let cap := A * (r*(n:ℝ)^(9/10:ℝ)) * (growth^T*width n α) * (logWidth r n:ℝ)^D
      ∀ (M : ℕ), (M:ℝ)≤cap →
      ∀ (σ : Type) [Fintype σ] (O : ℕ → Type) (W G : ℕ → ℕ → Type)
        [∀ t, Fintype (O t)] [∀ t j, Fintype (W t j)] [∀ t j, Fintype (G t j)]
        (f : Frame σ (O 0)) (inner : ∀ t, t<T → Steps k b (W t) (G t))
        (pre : ∀ t, t<T → Frame (Fin (k^b) × O t) (Fin (k^b) × W t 0))
        (post : ∀ t, t<T → Frame ((Fin (k^b) × O t) ⊕ W t b) (O (t+1))),
        f.size+1 ≤ M → (∀ t (ht : t<T), (pre t ht).size ≤ M ∧ (post t ht).size ≤ M) →
        (∀ t (ht : t<T) j (hj : j<b), (inner t ht j hj).size + (2*k+4) ≤ M) →
        (∀ t<T, ∀ j<b, Fintype.card (G t j) ≤ M) →
        ((Q*(compile (nestedSteps inner pre post) T le_rfl (repeatLeaf (k^b) f T)).size +
          Fintype.card (Slot (k^b) (fun t => Slot k (G t) b) T) : ℕ) : ℝ) < r*(n:ℝ)^(92/100:ℝ) := by
  have hteam : τ*Real.logb 2 ((k^b)^1 : ℕ) ≤ α := by simpa using hteams
  have hβ : 2*α+9/10+1/100+τ/2000 < (183:ℝ)/200 := by linarith
  obtain ⟨ω,hω,hwork⟩ := eventually_historyTreeCost_below 1 D hα hτ hτ' (pow_pos hk b) hteam hg hgrowth _ hβ
  refine ⟨ω,hω,fun A hA => ?_⟩
  let factor := epochFactor k b
  filter_upwards [hwork (factor*A) (by positivity),
    eventually_rpow_gap (show (183:ℝ)/200 < 92/100 by norm_num) (Q+1)] with n hb gap
  intro r hr hr' T cap M hM σ _ O W G _ _ _ f inner pre post hf hio hn hw
  have bound := hb r hr hr'
  dsimp only at bound
  simp only [Nat.one_mul] at bound
  have hcap : ((factor*M:ℕ):ℝ) ≤ (factor*A)*(r*(n:ℝ)^(9/10:ℝ))*(growth^T*width n α)*(logWidth r n:ℝ)^D := by
    push_cast
    calc
      _ ≤ factor*cap := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg _)
      _ = _ := by dsimp [cap]; ring
  have hfac : 0<factor := by dsimp [factor,epochFactor]; omega
  have hleaf : ((f.size+1:ℕ):ℝ) ≤ (factor*M:ℕ) := by exact_mod_cast hf.trans (Nat.le_mul_of_pos_left M hfac)
  let steps := nestedSteps inner pre post
  let fs := repeatLeaf (k^b) f T
  have hg := compile_size steps T le_rfl fs f.size (factor*M) (repeated_size _ _ _)
    (fun t ht => nestedSteps_size inner pre post hk M (by omega) t ht (hio t ht).1 (hio t ht).2 (hn t ht))
  have hs := slot_card_le (k^b) (fun t => Slot k (G t) b) T (factor*M)
    (fun t ht => nestedSlots_size k b M hk (G t) (hw t ht))
  have gate : ((compile steps T le_rfl fs).size : ℝ) < r*(n:ℝ)^(183/200:ℝ) :=
    (by exact_mod_cast hg : ((compile steps T le_rfl fs).size : ℝ) ≤ historyTreeCost (k^b) (f.size+1) (factor*M) T).trans_lt
      (bound (f.size+1) (factor*M) (hleaf.trans hcap) hcap)
  have slots : (Fintype.card (Slot (k^b) (fun t => Slot k (G t) b) T):ℝ) < r*(n:ℝ)^(183/200:ℝ) :=
    (by exact_mod_cast hs : (Fintype.card (Slot (k^b) (fun t => Slot k (G t) b) T):ℝ) ≤
        historyTreeCost (k^b) 0 (factor*M) T).trans_lt
      (bound 0 (factor*M) (by simpa using (Nat.cast_nonneg (factor*M)).trans hcap) hcap)
  push_cast
  calc
    _ < (Q:ℝ)*(r*(n:ℝ)^(183/200:ℝ)) + r*(n:ℝ)^(183/200:ℝ) :=
      add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left gate.le (Nat.cast_nonneg _)) slots
    _ = r*((Q+1)*(n:ℝ)^(183/200:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left gap (Nat.cast_nonneg _)

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
