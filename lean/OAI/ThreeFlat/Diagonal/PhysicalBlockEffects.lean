import OAI.ThreeFlat.Diagonal.PhysicalProgramEffects

namespace OAI
/-! # The ordered effects of a repeated shrink–refresh block -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block

noncomputable section
variable {F : Type} [Field F] (B : Block F)

/-- The effect of the shrink from level `i` to level `i+1`. -/
def shrinkEffect (cost : ShrinkMotif.Table F → ℕ → ℕ → ℝ) (i : ℕ) : Effect :=
  ⟨126/127, max 0 (cost B.shrink (B.exponent i) (2 ^ B.exponent (i+1))), true⟩

/-- The refresh after the final shrink restores the original degree. -/
def refreshEffect : Effect :=
  ⟨max 0 ((1+B.h+B.pad : ℕ) + 2*(RefreshMotif.leading B.h (1+B.h+B.pad) B.γ+1) : ℝ),
    B.refresh.error, false⟩

/-- The successive shrink effects over `n` levels, starting at level `i`. -/
def shrinkEffects (cost : ShrinkMotif.Table F → ℕ → ℕ → ℝ) : ℕ → ℕ → List Effect
  | 0, _ => []
  | n+1, i => B.shrinkEffect cost i :: shrinkEffects cost n (i+1)

/-- All the ordered shrink effects followed by the single refresh. -/
def oneBlockEffects (cost : ShrinkMotif.Table F → ℕ → ℕ → ℝ) : List Effect :=
  B.shrinkEffects cost B.levels 0 ++ [B.refreshEffect]

variable (cost : ShrinkMotif.Table F → ℕ → ℕ → ℝ)

/-- An offset `j < n` contributes precisely the shrink at the absolute level `i+j`. -/
theorem shrinkEffects_eq_ofFn (n i : ℕ) :
    B.shrinkEffects cost n i = List.ofFn (fun j : Fin n ↦ B.shrinkEffect cost (i+j.val)) := by
  induction n generalizing i with
  | zero => simp only [shrinkEffects, List.ofFn_zero]
  | succ n ih =>
    simp only [shrinkEffects, List.ofFn_succ, ih, Fin.val_zero, Fin.val_succ, Nat.add_zero,
      Nat.succ_add, Nat.add_succ]

theorem effects_shrinkPrefix (n i : ℕ) (tail : Program F (B.exponent (i+n))) :
    (B.shrinkPrefix n i tail).effects cost = B.shrinkEffects cost n i ++ tail.effects cost := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [shrinkPrefix, Program.effects, ih, Program.effects_cast, shrinkEffects,
      shrinkEffect, List.cons_append]

theorem effects_prefix (tail : Program F (B.exponent 0)) :
    (B.prefix tail).effects cost = B.oneBlockEffects cost ++ tail.effects cost := by
  simp only [«prefix», effects_shrinkPrefix, Program.effects_cast, Program.effects,
    oneBlockEffects, refreshEffect, List.append_assoc, List.cons_append, List.nil_append]

theorem effects_repeat_succ (n : ℕ) :
    (B.repeat (n+1)).effects cost = B.oneBlockEffects cost ++ (B.repeat n).effects cost :=
  B.effects_prefix cost (B.repeat n)

theorem effects_repeat (n : ℕ) :
    (B.repeat n).effects cost = (List.replicate n (B.oneBlockEffects cost)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [effects_repeat_succ, ih, List.replicate_succ, List.flatten_cons]

end
end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
