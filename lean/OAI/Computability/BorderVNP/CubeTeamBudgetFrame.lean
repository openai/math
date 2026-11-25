import OAI.Computability.BorderVNP.CubeTeamNativeFrame
import OAI.Computability.BorderVNP.CubeISALengthScan

/-! # Exact word limits for the team budgets in Section 8.2 -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamBudget

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Number of teams, crossing scale from (7.2), and the team-total array. -/
structure Layout where
  /-- Physical team count. -/
  teams : ℕ
  /-- Public length-dependent scale, frame 31. -/
  X₀ : ℕ
  /-- Pointer to the total weight of each team. -/
  totals : ℕ

/-- Maximum integer team weight in millionths. -/
def Layout.teamLimit (l : Layout) := 1000000*l.X₀/256

/-- Maximum aggregate integer weight in millionths. -/
def Layout.totalLimit (l : Layout) := 1000000*l.X₀*l.teams/1024

/-- The individual integer comparison expresses exactly the paper's rational limit. -/
theorem Layout.le_teamLimit (l : Layout) (v : ℕ) :
    v ≤ l.teamLimit ↔ TeamNative.unscale v ≤ (l.X₀ : ℚ)/256 := by
  rw [Layout.teamLimit,Nat.le_div_iff_mul_le (by decide),TeamNative.unscale,
    div_le_div_iff₀ (by norm_num) (by norm_num)]
  norm_cast
  rw [Nat.mul_comm 1000000 l.X₀]

/-- The aggregate integer comparison expresses the rational aggregate cap. -/
theorem Layout.le_totalLimit (l : Layout) (v : ℕ) :
    v ≤ l.totalLimit ↔ TeamNative.unscale v ≤ (l.X₀ : ℚ)*l.teams/1024 := by
  rw [Layout.totalLimit,Nat.le_div_iff_mul_le (by decide),TeamNative.unscale,
    div_le_div_iff₀ (by norm_num) (by norm_num)]
  norm_cast
  rw [mul_comm (l.X₀*l.teams) 1000000, ← Nat.mul_assoc]

/-- Public frame words read at entry. -/
structure Layout.Fields (l : Layout) (frame : ℕ) (m : ℕ → ℕ) : Prop where
  teams : m (frame+1) = l.teams
  X₀ : m (frame+31) = l.X₀
  totals : m (frame+76) = l.totals

/-- Word bounds for preparing limits and addressing all the total words. -/
structure Layout.Fits (l : Layout) (frame w : ℕ) : Prop where
  frameFit : frame+76 < 2^w
  million : 1000000 < 2^w
  scaled : 1000000*l.X₀ < 2^w
  allScaled : 1000000*l.X₀*l.teams < 2^w
  address : ∀ i < l.teams, l.totals+i < 2^w

/-- Start the two budget tests from the actual allocated frame.
Register 5 holds the remaining aggregate allowance. -/
def setup : Code := .block [.constant 0 0,.constant 1 1,
  readFrame 2 62 63 1, readFrame 3 62 63 76, readFrame 7 62 63 31,
  .constant 8 100,.binary .mul 9 8 8,.binary .mul 9 9 8,.binary .mul 9 9 7,
  .constant 10 128,.binary .add 10 10 10,.binary .div 4 9 10,
  .binary .add 10 10 10,.binary .add 10 10 10,.binary .mul 9 9 2,.binary .div 5 9 10]

/-- Sum of the initial segment of actual team-total words. -/
def Layout.prefix (l : Layout) (mem : ℕ → ℕ) (i : ℕ) := ∑ k ∈ Finset.range i, mem (l.totals+k)

/-- Successful scan state, including exact remaining budget and all memory words. -/
structure Prefix (l : Layout) (m : ℕ → ℕ) (i : ℕ) (z : NatState) : Prop where
  mem : z.mem = m
  cursor : z.reg 0 = i
  one : z.reg 1 = 1
  teams : z.reg 2 = l.teams
  totals : z.reg 3 = l.totals
  limit : z.reg 4 = l.teamLimit
  remaining : z.reg 5 = l.totalLimit - l.prefix m i
  within : l.prefix m i ≤ l.totalLimit

/-- Actual frame reads return both integer caps and the empty prefix. -/
theorem run_setup {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w)
    (h : l.Fields (readings pub 0) (readings m)) (fit : l.Fits (readings pub 0) w) :
    BoundedRun pub macros setup s m setup.slots (Prefix l (readings m) 0) := by
  have safe (d : Reg) (f : Word 8) (z : NatState) (hf : f.val ≤ 76) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe d f _ z w (by have := fit.frameFit; omega)
  apply (setup.runFixed pub macros s m ?_).mono le_rfl
  · rintro z rfl
    constructor <;>
      simp (config := {decide := true}) [setup,Code.block,Code.fixedEval,readFrame_fixedEval,
        Code.evalNat,addressOp,NatState.ofWords,Layout.teamLimit,Layout.totalLimit,Layout.prefix,
        h.teams,h.totals,h.X₀]
  · simp (config := {decide := true}) [setup,Code.block,Code.fixedSafe,Code.safeReadOnly,
      Code.fixedEval,readFrame_fixedEval,Code.evalNat,addressOp,addressOpFits,NatState.ofWords,
      safe _ _ _ (by decide : (1:Word 8).val ≤ 76),safe _ _ _ (by decide : (76:Word 8).val ≤ 76),
      safe _ _ _ (by decide : (31:Word 8).val ≤ 76), h.teams,h.X₀,fit.million,fit.scaled,fit.allScaled]
    have hv := fit.million
    have hw : w ≠ 0 := by rintro rfl; simp at hv
    omega

end Cube.TeamBudget

end BorderVNP
end Computability
end OAI
