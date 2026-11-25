import OAI.ThreeFlat.Diagonal.PhysicalRunWidth
import OAI.ThreeFlat.Diagonal.PhysicalBlockWidthCost

namespace OAI
/-! # Largest individual wire on each repeated physical history -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block

noncomputable section
variable {F : Type} [Field F] (B : Block F)

theorem repeat_widthCeiling (n rem : ℕ) (A : State (2^(B.exponent 0)) ((B.repeat n).charge+rem)) :
    ((B.repeat n).run rem A).WidthCeiling ((A.maxWidth+1)*B.widthBase^n) := by
  simpa only [B.widthCost_repeat_eq_pow] using (B.repeat n).run_widthCeiling rem A

/-- Every read of the largest wire along the concrete admitted history,
including its initial and terminal state, fits this uniform bound. -/
theorem history_maxWidth (n rem : ℕ) (A : State (2^(B.exponent 0)) ((B.repeat n).charge+rem))
    (h : ((B.repeat n).run rem A).plan.History) (w : ℕ)
    (hw : w ∈ ((B.repeat n).run rem A).readStages (fun X => X.maxWidth) h) :
    w+1 ≤ (A.maxWidth+1)*B.widthBase^n :=
  Run.widthCeiling_history _ (B.repeat_widthCeiling n rem A) h w hw

theorem terminal_maxWidth (n rem : ℕ) (A : State (2^(B.exponent 0)) ((B.repeat n).charge+rem))
    (h : ((B.repeat n).run rem A).plan.History) :
    ((B.repeat n).run rem A).readTerminal (fun X => X.maxWidth) h + 1 ≤
      (A.maxWidth+1)*B.widthBase^n :=
  Run.widthCeiling_terminal _ (B.repeat_widthCeiling n rem A) h

theorem history_maxWidth_u8 (u rem : ℕ) (A : State (2^(B.exponent 0)) ((B.repeat (u^8)).charge+rem))
    (h : ((B.repeat (u^8)).run rem A).plan.History) (w : ℕ)
    (hw : w ∈ ((B.repeat (u^8)).run rem A).readStages (fun X => X.maxWidth) h) :
    w ≤ (A.maxWidth+1)*B.widthBase^((B.levels+1)*u^8) := by
  have h1 := B.history_maxWidth (u^8) rem A h w hw
  apply (Nat.le_succ _).trans (h1.trans _)
  exact Nat.mul_le_mul_left _ (by simpa only [B.widthCost_repeat_eq_pow] using B.widthCost_repeat_le (u^8))

end
end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
