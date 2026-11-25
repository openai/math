import OAI.ThreeFlat.Diagonal.PhysicalRepeatEnergy
import OAI.ThreeFlat.Diagonal.PhysicalReadHistory
import OAI.ThreeFlat.Diagonal.TraceCursorState

namespace OAI
/-! # Terminal edge labels of the repeated physical program -/

namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction Computability.VPVNP.Compression
noncomputable section
variable {F : Type} [Field F]

theorem State.widthSum_le_root {d l : ℕ} (A : State d l) :
    (A.widthSum:ℝ) ≤ Real.sqrt A.energy := by
  by_cases hd : d=0
  · subst d
    have h : A.widthSum=0 := by simp [State.widthSum]
    simpa only [h,Nat.cast_zero] using Real.sqrt_nonneg A.energy
  · exact A.widthSum_le_sqrt_energy (Nat.pos_of_ne_zero hd)

theorem State.boundary_card {d l : ℕ} (A : State d l) :
    Nat.card A.shape.Boundary = 2^A.widthSum := by
  classical
  change Nat.card (∀ e : (A.Base × Fin d) × BitWord l,Fin (2^A.width e)) = _
  rw [Nat.card_eq_fintype_card,Fintype.card_pi]
  simp only [Fintype.card_fin,State.widthSum,Finset.prod_pow_eq_pow_sum]

theorem Run.terminal_boundary_card {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) :
    Nat.card (r.plan.finish h).Boundary = 2^(r.readTerminal (fun X => X.widthSum) h) := by
  have hh := terminal_relation (fun X => X.shape) (fun X => X.widthSum)
    (fun (S : Shape) w => Nat.card S.Boundary = 2^w) (fun X => X.boundary_card) r h
  simpa only [Run.terminal_shape] using hh

theorem Run.terminal_of_allLeaves {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (p : ℝ → ℕ → Prop) (hp : r.AllLeaves p) :
    p (r.readTerminal (fun X => X.energy) h) (r.readTerminal (fun X => X.positions) h) := by
  induction r with
  | done A => exact hp
  | step R next ih => exact ih h.1 (Run.tailHistory R next h) (hp h.1)

namespace Block
variable (B : Block F)

/-- The actual final graph in this same history has exponentially fewer wire bits. -/
theorem history_terminal_width (n rem : ℕ) (A : State (2^B.exponent 0) ((B.repeat n).charge+rem))
    (h : ((B.repeat n).run rem A).plan.History) :
    (((B.repeat n).run rem A).readTerminal (α := ℕ) (fun X => X.widthSum) h:ℝ) ≤
      (Real.sqrt A.energy + 4*Real.sqrt B.blockError*(A.positions:ℝ))/2^n := by
  let r := (B.repeat n).run rem A
  have a := r.terminal_of_allLeaves h _ (B.terminal_energy n rem A)
  have b := Run.terminal_relation (fun X => X.widthSum) (fun X => X.energy)
    (fun (w : ℕ) e => (w:ℝ) ≤ Real.sqrt e) (fun X => X.widthSum_le_root) r h
  exact b.trans a

/-- The number of terminal bits after repeated compression of the physical cursor. -/
theorem cursor_history_terminal_width (n rem low offsets slots : ℕ)
    (hk : 2 ≤ (B.repeat n).charge+rem)
    (h : ((B.repeat n).run rem (B.cursorState hk low offsets slots)).plan.History) :
    let k := (B.repeat n).charge+rem
    let sites : ℝ := (k*2^k:ℕ)
    let seed := sites*(2^(B.exponent 0):ℕ)*(2^low*(offsets*slots*3):ℕ)
    let r := (B.repeat n).run rem (B.cursorState hk low offsets slots)
    (r.readTerminal (α := ℕ) (fun X => X.widthSum) h:ℝ) ≤ (seed+4*Real.sqrt B.blockError*sites)/2^n := by
  intro k sites seed r
  let A := B.cursorState hk low offsets slots
  have start : Real.sqrt A.energy ≤ seed := B.cursorState_energy hk low offsets slots
  have hp : (A.positions:ℝ) = sites := by
    dsimp only [A,sites,k]
    rw [B.cursorState_positions]
  apply (B.history_terminal_width n rem A h).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [hp]
  linarith

end Block
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
