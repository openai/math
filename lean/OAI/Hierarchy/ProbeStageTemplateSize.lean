import OAI.Hierarchy.ProbeStageFabric
import OAI.Hierarchy.ProbeStageScale

namespace OAI
/-! # Group widths and total positions of the fixed subdivision template -/

namespace Hierarchy.ProbeStage

def Shape.DyadicBounds (h d : ℕ) (s : Shape) : Prop :=
  (s.span = 2^(9*digit h d+2) ∨ s.span = 2^(widthLog h d (rounds d))) ∧
    Fintype.card s.Group * s.span ≤ 4^(rounds d+1)*2^h

private theorem outer_material {h d j : ℕ} {G : Type} [Fintype G]
    (hd : 1 ≤ d) (depth : j ≤ rounds d) (size : Fintype.card G = (radix h d)^j) :
    let s := (enterSockets G (2^widthLog h d j) (radix h d) (radix_pos h d)).shape
    Fintype.card s.Group * s.span = 4^(j+1) * 2^h := by
  change Fintype.card (G × Fin (blocks (2^widthLog h d j) (radix h d))) *
    (radix h d * quota (radix h d)) = _
  rw [Fintype.card_prod,Fintype.card_fin,size,blocks_exact,outer_width]
  have split : 2^blockLog h d j * 2^(9*digit h d+2) = 2^widthLog h d j*4 := by
    rw [widthLog,pow_add,pow_add]
    ring
  rw [Nat.mul_assoc,split,← Nat.mul_assoc,material_exact hd depth,pow_succ]
  ring

theorem template_dyadic_aux {h d : ℕ} (hd : 1 ≤ d) (remaining : ℕ) :
    ∀ j : ℕ, j+remaining = rounds d → ∀ (G : Type) [Fintype G],
    Fintype.card G = (radix h d)^j → ∀ s ∈ (template (radix h d) (radix_pos h d) remaining
      G (2^widthLog h d j)).shapes, Shape.DyadicBounds h d s := by
  induction remaining with
  | zero =>
    intro j eq G _ size s mem
    have jeq : j = rounds d := by omega
    subst j
    simp only [template,Fabric.shapes,List.mem_singleton] at mem
    subst s
    refine ⟨Or.inr rfl,?_⟩
    change Fintype.card G * 2^widthLog h d (rounds d) ≤ _
    rw [size,material_exact hd le_rfl]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
  | succ r ih =>
    intro j eq G _ size s mem
    have depth : j < rounds d := by omega
    let outer := (enterSockets G (2^widthLog h d j) (radix h d) (radix_pos h d)).shape
    have exterior : Shape.DyadicBounds h d outer := by
      refine ⟨Or.inl (outer_width h d),?_⟩
      rw [show Fintype.card outer.Group * outer.span = 4^(j+1)*2^h from outer_material hd depth.le size]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
    have card : Fintype.card (G × Fin (radix h d)) = (radix h d)^(j+1) := by
      rw [Fintype.card_prod,Fintype.card_fin,size,pow_succ]
    change s ∈ ([outer] ++ ((template (radix h d) (radix_pos h d) r (G × Fin (radix h d))
      (innerSize (2^widthLog h d j) (radix h d))).shapes ++ [outer])) at mem
    simp only [List.mem_append,List.mem_singleton] at mem
    rcases mem with left | mid | right
    · simpa only [left] using exterior
    · rw [inner_exact depth] at mid
      exact ih (j+1) (by omega) _ card s mid
    · simpa only [right] using exterior

theorem template_dyadic {h d : ℕ} (hd : 1 ≤ d) :
    ∀ s ∈ (template (radix h d) (radix_pos h d) (rounds d) Unit (2^h)).shapes,
      Shape.DyadicBounds h d s := by
  have layout := congrArg (fun t : ℕ => (template (radix h d) (radix_pos h d) (rounds d) Unit (2^t)).shapes)
    (widthLog_start (h:=h) hd)
  intro s mem
  exact template_dyadic_aux (h:=h) hd (rounds d) 0 (by omega) Unit (by simp) s (layout.symm ▸ mem)

theorem Shape.DyadicBounds.span_lower {h d : ℕ} {s : Shape} (bounds : Shape.DyadicBounds h d s) :
    2^(9*digit h d) ≤ s.span := by
  rcases bounds.1 with out | center
  · rw [out]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · rw [center]
    apply Nat.pow_le_pow_right (by decide)
    unfold widthLog
    omega

/-- With fixed subdivision factor, even the largest number of groups in a
stage is a vanishing fraction of the number of original records. -/
theorem eventually_sparse_groups {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ s ∈ (template (radix h d) (radix_pos h d) (rounds d)
      Unit (2^h)).shapes, (Fintype.card s.Group : ℝ) ≤ ε*(2:ℝ)^h := by
  obtain ⟨K,large⟩ := exists_nat_gt ((4:ℝ)^(rounds d+1)/ε)
  filter_upwards [Filter.eventually_ge_atTop (K*(9*d))] with h hh
  intro s mem
  have bounds := template_dyadic hd s mem
  have ksmall : K ≤ digit h d := (Nat.le_div_iff_mul_le (by omega : 0<9*d)).mpr hh
  have kspan : K ≤ s.span := (Nat.lt_two_pow_self (n:=K)).le.trans
    ((Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : K≤9*digit h d)).trans bounds.span_lower)
  have realSpan : (K:ℝ) ≤ s.span := by exact_mod_cast kspan
  have eps := ((div_lt_iff₀ hε).mp large).le.trans (mul_le_mul_of_nonneg_right realSpan hε.le)
  have slots : (Fintype.card s.Group : ℝ) * s.span ≤ (4:ℝ)^(rounds d+1)*2^h := by
    exact_mod_cast bounds.2
  have pos : (0:ℝ)<s.span := by exact_mod_cast (pow_pos (by decide : 0<2) _).trans_le bounds.span_lower
  apply (mul_le_mul_iff_left₀ pos).mp
  calc
    _ ≤ (4:ℝ)^(rounds d+1)*2^h := slots
    _ ≤ _ := (mul_le_mul_of_nonneg_right eps (by positivity : (0:ℝ)≤2^h)).trans_eq (by ring)

end Hierarchy.ProbeStage

end OAI
