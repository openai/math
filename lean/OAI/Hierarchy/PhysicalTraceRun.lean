import OAI.Hierarchy.PhysicalTraceContraction
import OAI.Hierarchy.PhysicalTracePins
import OAI.ThreeFlat.Diagonal.PhysicalTerminalWidths

namespace OAI
/-! # Repeated compression of the actual weighted verifier network -/

noncomputable section
namespace Hierarchy.TraceDistribution

open ThreeFlat LinearAlgebra.SpectralBooks
open Diagonal Diagonal.HistoryContraction Diagonal.LaneCursor
open scoped BigOperators Classical

variable {F : Type} [Field F]

namespace Physical

variable (B : PhysicalStage.Block F) {k : ℕ} (hk : 2≤k+1) (low offsets slots : ℕ)

/-- A single string encodes the selected *actual* terminal edge labels without
multiplicity. Its length has the factor-two saving at every block. -/
theorem boundary_string (B : PhysicalStage.Block F) (s rem low offsets slots : ℕ)
    (enough : 2 ≤ (B.repeat s).charge+rem)
    (h : ((B.repeat s).run rem (B.cursorState enough low offsets slots)).plan.History) :
    let k := (B.repeat s).charge+rem
    let positions : ℝ := (k*2^k:ℕ)
    let arcWidth : ℝ := (2^low*(offsets*slots*3):ℕ)
    let r := (B.repeat s).run rem (B.cursorState enough low offsets slots)
    ∃ bits : ℕ, Nonempty ((r.plan.finish h).Boundary ≃ (Fin bits → Bool)) ∧
      (bits:ℝ) ≤ (positions*(2^(B.exponent 0):ℕ)*arcWidth+
        4*Real.sqrt B.blockError*positions)/2^s := by
  intro k positions arcWidth r
  let bits := r.readTerminal (fun A => A.widthSum) h
  refine ⟨bits,?_,B.cursor_history_terminal_width s rem low offsets slots enough h⟩
  apply Fintype.card_eq.mp
  rw [←Nat.card_eq_fintype_card,r.terminal_boundary_card]
  simp [bits]

private theorem boundary_after_recast (B : PhysicalStage.Block F) {lanes : ℕ}
    (enough : 2 ≤ lanes) (s rem low offsets slots : ℕ) (e : lanes = (B.repeat s).charge+rem) :
    let A := B.cursorState enough low offsets slots
    let r := PhysicalStage.Program.recast e A ((B.repeat s).run rem (e ▸ A))
    ∀ h : r.plan.History, ∃ bits : ℕ, Nonempty ((r.plan.finish h).Boundary ≃ (Fin bits → Bool)) ∧
      (bits:ℝ) ≤ (((lanes*2^lanes:ℕ):ℝ)*(2^(B.exponent 0):ℕ)*(2^low*(offsets*slots*3):ℕ)+
        4*Real.sqrt B.blockError*((lanes*2^lanes:ℕ):ℝ))/2^s := by
  subst lanes
  exact boundary_string B s rem low offsets slots enough

/-- The bit saving applies to the same transported run used by the native
scalar factorization, including when the number of spare lane bits is zero. -/
theorem run_boundary (s low offsets slots : ℕ) (fits : B.blockCharge*s ≤ k+1)
    (h : (run B hk low offsets slots s fits).plan.History) :
    let Q := (run B hk low offsets slots s fits).plan
    let n := k+1
    ∃ bits : ℕ, Nonempty ((Q.finish h).Boundary ≃ (Fin bits → Bool)) ∧
      (bits:ℝ) ≤ (((n*2^n:ℕ):ℝ)*(2^(B.exponent 0):ℕ)*(2^low*(offsets*slots*3):ℕ)+
        4*Real.sqrt B.blockError*((n*2^n:ℕ):ℝ))/2^s := by
  have e : k+1=(B.repeat s).charge+(k+1-(B.repeat s).charge) := by rw [B.charge_repeat]; omega
  exact boundary_after_recast B hk s (k+1-(B.repeat s).charge) low offsets slots e h

/-- The same canonical shared label used in the contraction fits the
cap-sized budget after multiplication by the achieved saving. -/
theorem terminal_bits_volume (B : PhysicalStage.Block F) :
    ∃ C : ℕ, ∀ {k w u low slots s : ℕ} (hk : 2≤k+1)
      (_dim : k+1=u+1-low) (_room : low≤u+1) (_depth : u+1≤64*w)
      (_cells : slots≤10^26*(64*w+1)^14) (fits : B.blockCharge*s≤k+1),
      let Q := (run B hk low (1+(u+1+(u+1))) slots s fits).plan
      ∀ h : Q.History, ∃ bits : ℕ, Nonempty ((Q.finish h).Boundary ≃ (Fin bits → Bool)) ∧
        bits*2^s ≤ C*2^u*(w+1)^16 := by
  obtain ⟨slack,hs⟩ := exists_nat_ge (4*Real.sqrt B.blockError)
  obtain ⟨C,cap⟩ := terminal_volume (2^B.exponent 0) slack
  refine ⟨C,?_⟩
  intro k w u low slots s hk dim room depth cells fits Q h
  obtain ⟨bits,bijection,hb⟩ := run_boundary B hk s low (1+(u+1+(u+1))) slots fits h
  refine ⟨bits,bijection,?_⟩
  have natBound := cap w u low slots room depth cells
  dsimp only at natBound hb
  rw [← dim] at natBound
  have realBound :
      (((k+1)*2^(k+1):ℕ):ℝ)*(2^(B.exponent 0):ℕ)*(2^low*((1+(u+1+(u+1)))*slots*3):ℕ)+
      (slack:ℝ)*(((k+1)*2^(k+1):ℕ):ℝ) ≤ (C*2^u*(w+1)^16:ℕ) := by exact_mod_cast natBound
  have save := (le_div_iff₀ (by positivity : (0:ℝ)<2^s)).mp hb
  have extra := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α:=ℝ) ((k+1)*2^(k+1)))
  exact_mod_cast (save.trans ((add_le_add le_rfl extra).trans realBound))

end Physical


end Hierarchy.TraceDistribution

end
end OAI
