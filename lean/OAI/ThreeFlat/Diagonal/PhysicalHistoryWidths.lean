import OAI.ThreeFlat.Diagonal.PhysicalPrefixBudget
import OAI.ThreeFlat.Diagonal.PhysicalTerminalWidths
import Mathlib.Data.List.Forall2

namespace OAI
/-! # Wire sums for the exact graph histories admitted by the repeated physical program -/

namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction Computability.VPVNP.Compression
noncomputable section
variable {F : Type} [Field F]

private theorem Run.observable_budget (read : ∀ {d l},State d l → ℕ) (measure : Totals → ℝ)
    (valid : ∀ {d l} (X : State d l) (z : Totals),X.Within z → (read X:ℝ) ≤ measure z)
    {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (us : List Effect) (v : Totals) (hb : r.Budgeted us v) :
    List.Forall₂ (fun (a : ℕ) (b : Totals) => (a:ℝ) ≤ measure b)
      (r.readStages read h) (us.scanl Effect.apply v) := by
  induction r generalizing us v with
  | done A =>
    cases us with
    | nil => exact .cons (valid A v hb) .nil
    | cons => exact False.elim hb
  | @step d l D L A R next ih =>
    cases us with
    | nil => exact False.elim hb
    | cons u us =>
      rw [List.scanl_cons]
      exact .cons (valid A v hb.1) (ih h.1 (Run.tailHistory R next h) us (u.apply v) (hb.2 h.1))

private theorem observable_sum (measure : Totals → ℝ) (xs : List ℕ) (ys : List Totals) (b : ℝ)
    (h : List.Forall₂ (fun (a : ℕ) (w : Totals) => (a:ℝ) ≤ measure w) xs ys)
    (all : ∀ w ∈ ys, measure w ≤ b) : (xs.sum:ℝ) ≤ ys.length*b := by
  induction h with
  | nil => simp
  | @cons x y xs ys h rest ih =>
    have head := h.trans (all _ List.mem_cons_self)
    have tail := ih (fun w hw => all w (List.mem_cons_of_mem _ hw))
    simp only [List.sum_cons,Nat.cast_add,List.length_cons,Nat.cast_succ]
    linarith

namespace Block
variable (B : Block F)

theorem repeat_effects_length (n : ℕ) : ((B.repeat n).effects shrinkError).length = (B.levels+1)*n := by
  induction n with
  | zero => simp [«repeat»,Program.effects]
  | succ n ih =>
    rw [B.effects_repeat_succ,List.length_append,ih]
    simp only [oneBlockEffects,List.length_append,B.shrinkEffects_length,List.length_cons,List.length_nil,Nat.mul_succ]
    omega

/-- The sum of wire widths, taken over all stages of a single ordered, admitted history. -/
theorem history_widths (n rem : ℕ) (A : State (2^B.exponent 0) ((B.repeat n).charge+rem))
    (h : ((B.repeat n).run rem A).plan.History) :
    ((((B.repeat n).run rem A).readStages (α := ℕ) (fun X => X.widthSum) h).sum:ℝ) ≤
      (((B.levels+1)*n+1:ℕ):ℝ)*(Real.sqrt B.stageGrowth*B.initialBudget ⟨A.energy,A.positions⟩) := by
  let v : Totals := ⟨A.energy,A.positions⟩
  let us := (B.repeat n).effects shrinkError
  have hb := (B.repeat n).run_budgeted rem A v ⟨le_rfl,le_rfl⟩
  have compare := ((B.repeat n).run rem A).observable_budget (fun X => X.widthSum)
    (fun z => Real.sqrt z.energy) (fun X _ hX => X.widthSum_le_root.trans (Real.sqrt_le_sqrt hX.1)) h us v hb
  have bound := observable_sum _ _ _ _ compare (B.scan_energy n v ⟨A.energy_nonneg,by dsimp [v]; positivity⟩)
  simpa only [us,List.length_scanl,B.repeat_effects_length] using bound

private theorem sites_of_scan (us : List Effect) (v : Totals) (hp : 0≤v.sites)
    (w : Totals) (hw : w ∈ us.scanl Effect.apply v) : w.sites ≤ v.sites := by
  induction us generalizing v w with
  | nil =>
    have eq : w=v := by simpa using hw
    rw [eq]
  | cons u us ih =>
    rw [List.scanl_cons,List.mem_cons] at hw
    rcases hw with rfl|ht
    · exact le_rfl
    · have p : 0≤(u.apply v).sites ∧ (u.apply v).sites ≤ v.sites := by
        cases h : u.shrink <;> simp only [Effect.apply,h,Bool.false_eq_true,ite_false,ite_true]
        · exact ⟨hp,le_rfl⟩
        · exact ⟨by positivity,by linarith⟩
      exact (ih _ p.1 _ ht).trans p.2

theorem history_positions (n rem : ℕ) (A : State (2^B.exponent 0) ((B.repeat n).charge+rem))
    (h : ((B.repeat n).run rem A).plan.History) :
    (((B.repeat n).run rem A).readStages (fun X => X.positions) h).sum ≤
      ((B.levels+1)*n+1)*A.positions := by
  let v : Totals := ⟨A.energy,A.positions⟩
  let us := (B.repeat n).effects shrinkError
  have hb := (B.repeat n).run_budgeted rem A v ⟨le_rfl,le_rfl⟩
  have compare := ((B.repeat n).run rem A).observable_budget (fun X => X.positions)
    Totals.sites (fun _ _ hX => hX.2) h us v hb
  have bound := observable_sum _ _ _ _ compare (sites_of_scan us v (by dsimp [v]; positivity))
  simp only [us,v,List.length_scanl,B.repeat_effects_length] at bound
  exact_mod_cast bound

/-- Both estimates for the actual cursor placement, with its displayed slot width and site count. -/
theorem cursor_history_widths (n rem low offsets slots : ℕ)
    (hk : 2 ≤ (B.repeat n).charge+rem)
    (h : ((B.repeat n).run rem (B.cursorState hk low offsets slots)).plan.History) :
    let k := (B.repeat n).charge+rem
    let sites : ℝ := (k*2^k:ℕ)
    let seed := sites*(2^(B.exponent 0):ℕ)*(2^low*(offsets*slots*3):ℕ)
    let r := (B.repeat n).run rem (B.cursorState hk low offsets slots)
    ((r.readStages (α := ℕ) (fun X => X.widthSum) h).sum:ℝ) ≤
        (((B.levels+1)*n+1:ℕ):ℝ) * (Real.sqrt B.stageGrowth*(seed+(4*Real.sqrt B.blockError+1)*sites)) ∧
    (r.readTerminal (α := ℕ) (fun X => X.widthSum) h:ℝ) ≤ (seed+4*Real.sqrt B.blockError*sites)/2^n := by
  intro k sites seed r
  let A := B.cursorState hk low offsets slots
  have start : Real.sqrt A.energy ≤ seed := B.cursorState_energy hk low offsets slots
  have hp : (A.positions:ℝ) = sites := by
    dsimp only [A,sites,k]
    rw [B.cursorState_positions]
  constructor
  · apply (B.history_widths n rem A h).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    dsimp only [initialBudget,potential]
    rw [hp]
    linarith
  · exact B.cursor_history_terminal_width n rem low offsets slots hk h

end Block
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
