import OAI.Computability.BorderVNP.PackedProfiles

/-! # Resource bounds along a selected profile history

At each node the recorded history chooses one of the actual outputs of Lemma 6.1 after its
`K` input histories have been fixed. The potential and the two local maxima are propagated over
these exact choices. The public work sums over the nodes of this selected tree.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open Finset

variable {Pack : ℕ → Type*} {K : ℕ} (bottom : Pack 0)
    (epoch : ∀ t, (Fin K → Pack t) → ProfileSum (Pack (t + 1)))

/-- Induction over histories permits the next epoch to depend on all the previous profiles. -/
theorem history_induction (P : ∀ t, Pack t → Prop) (h0 : P 0 bottom)
    (hstep : ∀ t child, (∀ i, P t (child i)) → ∀ q, P (t+1) ((epoch t child).term q)) :
    ∀ t (q : (packHistory bottom epoch t).Index), P t ((packHistory bottom epoch t).term q) := by
  intro t
  induction t with
  | zero => exact fun _ => h0
  | succ t ih => exact fun q => hstep t _ (fun i => ih (q.1 i)) q.2

private def childMax {α : Type*} [LinearOrder α] (hK : 0 < K) (x : Fin K → α) : α :=
  univ.sup' ⟨⟨0, hK⟩, mem_univ _⟩ x

private theorem childMax_le {α : Type*} [LinearOrder α] (hK : 0 < K) (x : Fin K → α)
    {M : α} (h : ∀ i, x i ≤ M) : childMax hK x ≤ M :=
  sup'_le _ _ fun i _ => h i

/-- Per-tile descriptor and expanded-weight estimates through all selected epochs.
Apply the theorem separately to the two measures, retaining earlier local boxes in each. -/
theorem history_local_bound (hK : 0 < K) (M : ∀ t, Pack t → ℕ) (C : ℕ)
    (step : ∀ t child q, M (t+1) ((epoch t child).term q) + 1 ≤
      C * ((univ.sup' ⟨⟨0, hK⟩, mem_univ _⟩ (fun i => M t (child i))) + 1)) :
    ∀ t (q : (packHistory bottom epoch t).Index),
      M t ((packHistory bottom epoch t).term q) + 1 ≤ C ^ t * (M 0 bottom + 1) := by
  apply history_induction bottom epoch (fun t p => M t p + 1 ≤ C^t * (M 0 bottom + 1)) (by simp)
  intro t child hc q
  have hm' : childMax hK (fun i => M t (child i)) + 1 ≤ C^t * (M 0 bottom + 1) := by
    obtain ⟨i, _, hi⟩ := exists_mem_eq_sup' ⟨⟨0, hK⟩, mem_univ _⟩ (fun i => M t (child i))
    rw [childMax, hi]
    exact hc i
  calc
    _ ≤ _ := step t child q
    _ ≤ C * (C^t * (M 0 bottom + 1)) := Nat.mul_le_mul_left C hm'
    _ = _ := by rw [pow_succ']; ring

/-- Normalizing (6.1) by the exact number of copies represented by each selected history
makes the largest input potential decay by a factor of two per epoch. -/
theorem history_potential_bound (hK : 0 < K) {b : ℕ} (hb : 0 < b)
    (I : ∀ t, Pack t → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (step : ∀ t child q, I (t+1) ((epoch t child).term q) / K ≤
      (univ.sup' ⟨⟨0, hK⟩, mem_univ _⟩ (fun i => I t (child i))) / 2 + A) :
    ∀ t (q : (packHistory bottom epoch t).Index),
      I t ((packHistory bottom epoch t).term q) / (b * (K : ℝ)^t) ≤
        (I 0 bottom / b) / 2 ^ t + 2 * A := by
  let f := fun (t : ℕ) => I 0 bottom / b / (2 : ℝ)^t + 2 * A
  let S := fun (t : ℕ) => (b : ℝ) * (K : ℝ)^t
  have hK' : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hb' : 1 ≤ (b : ℝ) := by exact_mod_cast hb
  have hS t : 1 ≤ S t := one_le_mul_of_one_le_of_one_le hb' (one_le_pow₀ hK')
  have hS0 t : 0 < S t := zero_lt_one.trans_le (hS t)
  have hK0 := zero_lt_one.trans_le hK'
  have hb0 := zero_lt_one.trans_le hb'
  suffices h : ∀ t (q : (packHistory bottom epoch t).Index),
      I t ((packHistory bottom epoch t).term q) ≤ f t * S t by
    exact fun t q => (div_le_iff₀ (hS0 t)).mpr (h t q)
  apply history_induction bottom epoch (fun t p => I t p ≤ f t * S t)
  · dsimp [f, S]
    simp only [pow_zero, div_one, mul_one]
    rw [add_mul, div_mul_cancel₀ _ hb0.ne']
    exact le_add_of_nonneg_right (by positivity)
  · intro t child hc q
    have hm := childMax_le hK (fun i => I t (child i)) hc
    have hraw : I (t+1) ((epoch t child).term q) ≤ (f t * S t / 2 + A) * K :=
      (div_le_iff₀ hK0).mp ((step t child q).trans (by change childMax hK _ / 2 + A ≤ _; linarith))
    calc
      _ ≤ _ := hraw
      _ ≤ (f t * S t / 2 + A * S t) * K := by
        gcongr; exact le_mul_of_one_le_right hA (hS t)
      _ = _ := by dsimp [f, S]; rw [pow_succ, pow_succ]; ring

/-- Public word operations performed by a single reconstruction, including every visited node. -/
def historyTicks (ticks : ∀ t, Pack t → ℕ) :
    (t : ℕ) → (packHistory bottom epoch t).Index → ℕ
  | 0, _ => ticks 0 bottom
  | t+1, q =>
    (∑ i, historyTicks ticks t (q.1 i)) + ticks (t+1) ((packHistory bottom epoch (t+1)).term q)

/-- With cost at most `M` per pack at every level, reconstruction of a single final history
takes at most `(T+1) K^T M` ticks. No work is charged for unused profile branches. -/
theorem historyTicks_le (hK : 0 < K) (ticks : ∀ t, Pack t → ℕ) (M T : ℕ)
    (hm : ∀ t ≤ T, ∀ q, ticks t ((packHistory bottom epoch t).term q) ≤ M)
    (q : (packHistory bottom epoch T).Index) :
    historyTicks bottom epoch ticks T q ≤ (T + 1) * K^T * M := by
  induction T with
  | zero =>
    change ticks 0 bottom ≤ _
    simpa using (show ticks 0 bottom ≤ M from hm 0 le_rfl q)
  | succ t ih =>
    have hchild (i : Fin K) := ih (fun j hj => hm j (by omega)) (q.1 i)
    have hsum : ∑ i : Fin K, historyTicks bottom epoch ticks t (q.1 i) ≤ K * ((t+1) * K^t * M) := by
      simpa using (sum_le_sum (s := univ) (fun i _ => hchild i))
    have hpos : 1 ≤ K ^ (t+1) := Nat.one_le_pow _ _ hK
    calc
      _ ≤ K * ((t+1) * K^t * M) + M := add_le_add hsum (hm _ le_rfl q)
      _ ≤ K * ((t+1) * K^t * M) + K^(t+1) * M := by
        gcongr; exact Nat.le_mul_of_pos_left M hpos
      _ = _ := by rw [pow_succ]; ring

end Packing

end BorderVNP
end Computability
end OAI
