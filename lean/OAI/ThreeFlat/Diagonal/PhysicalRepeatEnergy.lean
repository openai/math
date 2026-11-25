import OAI.ThreeFlat.Diagonal.PhysicalRunBudget
import OAI.ThreeFlat.Diagonal.PhysicalBlockEffects
import OAI.ThreeFlat.Diagonal.PhysicalEffectBounds
import OAI.ThreeFlat.Diagonal.BlockEnergyPotential

namespace OAI
/-! # Exponential decay on every terminal branch of the repeated physical program -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block
noncomputable section
variable {F : Type} [Field F] (B : Block F)

theorem shrinkEffects_length (n i : ℕ) : (B.shrinkEffects shrinkError n i).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [shrinkEffects,ih]

theorem shrinkEffects_spec (n i : ℕ) (u : Effect) (hu : u ∈ B.shrinkEffects shrinkError n i) :
    u.leading=126/127 ∧ 0≤u.error ∧ u.shrink=true := by
  induction n generalizing i with
  | zero => simp [shrinkEffects] at hu
  | succ n ih =>
    rcases List.mem_cons.mp hu with eq|mem
    · subst u
      exact ⟨rfl,le_max_left _ _,rfl⟩
    · exact ih (i+1) mem

/-- This fixed error depends only on the chosen block, including its two finite motif tables. -/
def blockError : ℝ := B.refreshEffect.leading*Effect.errors (B.shrinkEffects shrinkError B.levels 0)
    + B.refreshEffect.error

theorem blockError_nonneg : 0 ≤ B.blockError :=
  add_nonneg (mul_nonneg (le_max_left _ _)
    (Effect.errors_nonneg _ fun u hu => (B.shrinkEffects_spec _ _ u hu).2.1)) B.refresh.nonneg

def potential (v : Totals) : ℝ := Real.sqrt v.energy+(4*Real.sqrt B.blockError)*v.sites

theorem apply_block (v : Totals) (hv : v.Positive) :
    let w := (B.oneBlockEffects shrinkError).foldl Effect.apply v
    w.Positive ∧ B.potential w ≤ B.potential v / 2 := by
  let us := B.shrinkEffects shrinkError B.levels 0
  have spec := B.shrinkEffects_spec B.levels 0
  have len : us.length = B.levels := B.shrinkEffects_length _ _
  have hr : B.refreshEffect.Positive := ⟨le_max_left _ _,B.refresh.nonneg⟩
  have contracts : B.refreshEffect.leading*(126/127:ℝ)^us.length ≤ 1/4 := by
    rw [len]
    unfold refreshEffect
    cases le_total (((1+B.h+B.pad:ℕ):ℝ)+2*(RefreshMotif.leading B.h (1+B.h+B.pad) B.γ + 1)) 0 with
    | inl h => rw [max_eq_left h,zero_mul]; norm_num
    | inr h => simpa only [max_eq_right h] using B.contracts
  have bound := Effect.fold_block us B.refreshEffect v hv spec (by simpa only [len] using B.positive) hr rfl contracts
  constructor
  · have hpos : ∀ (ls : List Effect) (w : Totals), (∀ u ∈ ls,u.Positive) →
        w.Positive → (ls.foldl Effect.apply w).Positive := by
      intro ls
      induction ls with
      | nil => exact fun _ _ hw => hw
      | cons u xs ih =>
        intro w h hw
        exact ih _ (fun t ht => h _ (List.mem_cons_of_mem _ ht)) (u.apply_positive (h _ List.mem_cons_self) _ hw)
    apply hpos _ _ _ hv
    intro u mem
    rcases List.mem_append.mp mem with hu|hu
    · exact ⟨by rw [(spec u hu).1]; norm_num, (spec u hu).2.1⟩
    · have eq : u=B.refreshEffect := List.mem_singleton.mp hu
      simpa [eq] using hr
  · exact potential_half hv.1 hv.2 B.blockError_nonneg bound.1 bound.2

theorem repeat_potential (n : ℕ) (v : Totals) (hv : v.Positive) :
    let w := ((B.repeat n).effects shrinkError).foldl Effect.apply v
    w.Positive ∧ B.potential w ≤ B.potential v / 2^n := by
  induction n generalizing v with
  | zero => exact ⟨hv,by simp [Block.repeat,Program.effects]⟩
  | succ n ih =>
    rw [B.effects_repeat_succ,List.foldl_append]
    have step := B.apply_block v hv
    obtain ⟨hp,hl⟩ := ih _ step.1
    refine ⟨hp,hl.trans ?_⟩
    calc
      _ ≤ (B.potential v/2)/2^n := div_le_div_of_nonneg_right step.2 (by positivity)
      _ = _ := by rw [pow_succ,div_div,mul_comm (2:ℝ) (2^n)]

/-- Actual repeated histograms starting at the specific graph share this single bound,
including when their successor wire arrays differ. -/
theorem terminal_energy (n rem : ℕ) (A : State (2^(B.exponent 0)) ((B.repeat n).charge+rem)) :
    ((B.repeat n).run rem A).AllLeaves (fun E _ =>
      Real.sqrt E ≤ (Real.sqrt A.energy + (4*Real.sqrt B.blockError)*(A.positions:ℝ))/2^n) := by
  let v : Totals := ⟨A.energy,A.positions⟩
  let r := (B.repeat n).run rem A
  let us := (B.repeat n).effects shrinkError
  have hv : v.Positive := ⟨A.energy_nonneg,by dsimp [v]; positivity⟩
  have hb := (B.repeat n).run_budgeted rem A v ⟨le_rfl,le_rfl⟩
  have h := B.repeat_potential n v hv
  apply r.allLeaves_mono _ _ _ (r.allLeaves_of_budgeted us v hb)
  intro E p bounds
  apply (Real.sqrt_le_sqrt bounds.1).trans
  apply le_trans _ h.2
  dsimp only [potential]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) h.1.2)

end
end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
