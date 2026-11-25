import OAI.Computability.MultitapeWeakETH.ColorBudget
import OAI.Computability.MultitapeWeakETH.TypeCoding

/-! # Independent binary label rates for a source of prescribed type -/

namespace OAI.Computability.MultitapeWeakETH

open MatrixMultiplication MatrixMultiplication.Foundation
open ConditionalPrefixWords StageHierarchyResources LabelHierarchyCounts
open Filter
open scoped BigOperators Topology Classical

/-- Removing two rounded-up logarithms reserves a factor of r². -/
def colorBits (M r : ℕ) := Nat.log 2 M - 2*(Nat.log 2 r+1)

private theorem color_room {M r : ℕ} (pos : 0 < colorBits M r) :
    2^(colorBits M r)*r^2 ≤ M := by
  have h : 2*(Nat.log 2 r+1) ≤ Nat.log 2 M := by unfold colorBits at pos; omega
  have nz : M ≠ 0 := by rintro rfl; simp [colorBits] at pos
  calc
    _ ≤ 2^(colorBits M r)*(2^(Nat.log 2 r+1))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by decide) r).le 2)
    _ = 2^(Nat.log 2 M) := by
      rw [← pow_mul,← pow_add]; congr 1
      unfold colorBits; omega
    _ ≤ _ := Nat.pow_log_le_self 2 nz

private theorem binary_record_card (n : ℕ) :
    Fintype.card (LabelRecord (fun _ => Bool) n) = 2^n := by
  induction n with
  | zero => exact Fintype.card_punit
  | succ n ih => rw [pow_succ,← ih]; exact Fintype.card_prod _ _

/-- For sufficiently many repetitions the binary labels have the calculated
width on every coordinate. One fixed column-only coloring at each stage
realizes every tuple on a full source word of the prescribed type. -/
theorem exact_type_binary_labels {A : Type} [Fintype A] (counts : A → ℕ) (labels : ℕ → A → Bool)
    (depth t : ℕ) (separate : Function.Injective (labelRecordOf labels depth))
    (large : depth+1 < t*(∑ x, counts x)) :
    let r := t*(∑ x, counts x)
    let C := fun j : Fin depth => Fin (2^(colorBits (stageRefinementCount counts labels j t) r))
    ∃ color : (j : Fin depth) → (Fin r → Bool) → C j, ∀ target : (j : Fin depth) → C j,
      ∃ word : PopulationWords (Fin r) (fun x => t*counts x), ∀ j : Fin depth,
        color j (fun i => labels j (word.val i)) = target j := by
  intro r C
  apply exact_type_colors counts labels depth t separate C
  intro j
  let M := stageRefinementCount counts labels j t
  have pos : 0 < M := stageRefinementCount_pos counts labels j t
  have inhabitedPrefix (n : ℕ) : Nonempty (ExactPrefix counts labels n t (Fin r)) := by
    induction n with
    | zero => exact ⟨rootPrefixWord counts labels t (Fin r) (by simp [r,Finset.mul_sum])⟩
    | succ n ih =>
      obtain ⟨pre⟩ := ih
      exact ⟨appendCode pre ⟨0,stageRefinementCount_pos counts labels n t⟩⟩
  obtain ⟨pre⟩ := inhabitedPrefix j
  have cardWords : Fintype.card (Fin r → Bool) = 2^r := by simp
  have size : M ≤ 2^r := by
    rw [show M = stageRefinementCount counts labels j t from rfl,← conditionalFinset_card pre,← cardWords]
    exact Finset.card_le_univ _
  change (Fintype.card (ExactPrefix counts labels j t (Fin r))*Fintype.card (C j)) *
    ((Fintype.card (C j)-1)^M*(Fintype.card (C j))^(Fintype.card (Fin r → Bool)-M)) <
      (Fintype.card (C j))^Fintype.card (Fin r → Bool)
  simp only [C,Fintype.card_fin,cardWords]
  by_cases zero : colorBits M r = 0
  · dsimp only [M] at zero
    simp [zero,pos.ne']
  · apply coloring_budget_for_columns (j := j.val) (by positivity) _ _ size
      (color_room (Nat.pos_of_ne_zero zero)) (by dsimp [r]; omega)
    · apply (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
      simp [binary_record_card,← pow_mul,Nat.mul_comm]
    · exact (Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)).trans
        ((Nat.pow_log_le_self 2 pos.ne').trans size)

theorem colorBits_rate {M r : ℕ → ℕ} {H : ℝ} (grow : Tendsto r atTop atTop)
    (rate : Tendsto (fun t => Real.logb 2 (M t) / (r t : ℝ)) atTop (𝓝 H)) :
    Tendsto (fun t => (colorBits (M t) (r t) : ℝ)/(r t : ℝ)) atTop (𝓝 H) := by
  have times := tendsto_natCast_atTop_atTop (R := ℝ) |>.comp grow
  have vanishes : Tendsto (fun t => (2*Real.logb 2 (r t)+3)/(r t:ℝ)) atTop (𝓝 0) := by
    have logarithm := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp times
    have constant : Tendsto (fun t => (3:ℝ)/(r t:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop times
    have h := (((logarithm.div_const (Real.log 2)).const_mul 2).add constant)
    simp only [zero_div,mul_zero,add_zero] at h
    apply h.congr
    intro t
    simp only [Function.comp_apply,id_eq,Real.logb]
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using rate.sub vanishes) rate
  · filter_upwards with t
    have h₁ := Nat.lt_floor_add_one (Real.logb 2 (M t))
    rw [← show ((2:ℕ):ℝ) = 2 by norm_num,Real.natFloor_logb_natCast] at h₁
    have h₂ := Real.natLog_le_logb (r t) 2
    have sub : Nat.log 2 (M t) ≤ colorBits (M t) (r t)+2*(Nat.log 2 (r t)+1) := by
      unfold colorBits; omega
    have realSub := Nat.cast_le (α := ℝ) |>.mpr sub
    push_cast at realSub h₁ h₂
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith only [h₁,h₂,realSub]) (Nat.cast_nonneg _)
  · filter_upwards with t
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact (Nat.cast_le.mpr (Nat.sub_le ..)).trans (Real.natLog_le_logb (M t) 2)

end OAI.Computability.MultitapeWeakETH
