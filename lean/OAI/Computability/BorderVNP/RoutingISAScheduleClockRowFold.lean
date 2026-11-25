import OAI.Computability.BorderVNP.TransmissionStraight
import OAI.Computability.BorderVNP.RoutingISAScheduleClockLocalRoles
import OAI.Computability.BorderVNP.CubeTeamOwnedReturn

/-! # Local clocks on the chronological owned-row history

The physical owner word and the two symbols determine which callback runs
at each ordinal. Each claimed row is read only on its own visited side.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open BorderVNP.Cube BorderVNP.Cube.TeamRows TeamRowPrepare VPVNP.BurstRAM Finset

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {l : TeamRowPrepare.Layout}

private def rowBudget (l : TeamRowPrepare.Layout) (owner cost : ℕ → ℕ) (q : ℕ) :=
  TeamRowPrepare.prepare.slots+5+if owner (q/l.d)=l.teamID then cost q else 0

/-- Fold a measured local visit on the actual intermediate states and owner
words. The reachable-state predicate can track the live vertex cursor and
the exact source addresses for the next role. -/
theorem rows_traceCost {strict diagonal : Code} {q s m rows es t mt}
    (history : ReturnedRows pub mac l strict diagonal q s m rows es t mt)
    (owner cost : ℕ → ℕ) (I : ℕ → Word w → Memory w → Prop)
    (entry : I q (s 7) m)
    (skip : ∀ j < l.d*l.d, ∀ k mem, I j k mem → owner (j/l.d) ≠ l.teamID → I (j+1) k mem)
    (words : ∀ j < l.d*l.d, ∀ k mem, I j k mem → readings mem (l.ownerBase+j/l.d)=owner (j/l.d))
    (visitCost : ∀ j < l.d*l.d, ∀ u mu ys v mv, I j (u 7) mu → owner (j/l.d)=l.teamID →
      ReadyRow l (readings mu) j (.ofWords u mu) →
      Runs pub mac (if j/l.d=j%l.d then diagonal else strict) u mu ys v mv →
      traceCost ys ≤ cost j ∧ I (j+1) (v 7) mv) :
    traceCost es ≤ (∑ j ∈ Ico q (l.d*l.d),rowBudget l owner cost j)+1 := by
  induction history with
  | done => simp only [Ico_self,sum_empty,zero_add]; rfl
  | @row q s m ps ys a bs b mt c rs gs t mz more prep ready visit bump rest ih =>
    have control : a 7 = s 7 := prep.keepsReg prepare_keeps
    have after : c 7 = b 7 := bump.keepsReg (by decide)
    have entered : I q (a 7) m := control ▸ entry
    have word := words q more _ _ entered
    have role :
        traceCost ys ≤ (if owner (q/l.d)=l.teamID then cost q else 0) ∧ I (q+1) (b 7) mt := by
      cases visit with
      | skip miss =>
        have off : owner (q/l.d) ≠ l.teamID := word ▸ miss
        exact ⟨by simp [off,traceCost,VPVNP.RAMBuckets.cost],skip q more _ _ entered off⟩
      | offDiagonal on diff run =>
        have owned : owner (q/l.d) = l.teamID := word ▸ on
        rw [ite_eq_left owned]
        exact visitCost q more a m _ _ _ entered owned ready (by rwa [ite_eq_right diff])
      | onDiagonal on same run =>
        have owned : owner (q/l.d) = l.teamID := word ▸ on
        rw [ite_eq_left owned]
        exact visitCost q more a m _ _ _ entered owned ready (by rwa [ite_eq_left same])
    have tail := ih (after ▸ role.2)
    have cp := prep.cost_le_slots (by decide)
    have cb : traceCost bs ≤ 2 := bump.cost_le_slots (by decide)
    rw [sum_eq_sum_Ico_succ_bot more]
    dsimp only [rowBudget] at tail ⊢
    have tickCost {x : List (TeamRAM.Event w)} : traceCost (tick w::x)=1+traceCost x := rfl
    rw [tickCost,Transmission.cost_append,Transmission.cost_append,Transmission.cost_append,tickCost,tickCost]
    omega

/-- Charge all four portions of a returning owned-group program, even when
other teams' declaration rows have yet to be checked. -/
theorem ownedHistory_traceCost {n b h K sym : ℕ} {r m es t mt} (owner cost : ℕ → ℕ)
    (H : OwnedReturnTrace pub mac l n b h K sym r m es t mt)
    (I : ℕ → Word w → Memory w → Prop) (entry : I 0 (H.scanStart 7) m)
    (skip : ∀ j < l.d*l.d, ∀ k mem, I j k mem → owner (j/l.d) ≠ l.teamID → I (j+1) k mem)
    (words : ∀ j < l.d*l.d, ∀ k mem, I j k mem → readings mem (l.ownerBase+j/l.d)=owner (j/l.d))
    (visitCost : ∀ j < l.d*l.d, ∀ u mu ys v mv, I j (u 7) mu → owner (j/l.d)=l.teamID →
      ReadyRow l (readings mu) j (.ofWords u mu) →
      Runs pub mac (if j/l.d=j%l.d then diagonalRole n b h K sym else strictRole n b h K sym) u mu ys v mv →
      traceCost ys ≤ cost j ∧ I (j+1) (v 7) mv) :
    traceCost es ≤ 4+(TeamRows.ticks l owner cost+11) := by
  have start : traceCost H.startEvents ≤ 4 := H.start.cost_le_slots (by decide)
  have init := H.setup.cost_le_slots (by decide)
  have endCost : traceCost H.finishEvents ≤ 11 := H.finish.cost_le_slots (by decide)
  have rows := rows_traceCost H.history owner cost I entry skip words visitCost
  rw [H.chronology,Transmission.cost_append,Transmission.cost_append,Transmission.cost_append]
  rw [Nat.Ico_zero_eq_range] at rows
  unfold TeamRows.ticks
  dsimp only [rowBudget] at rows
  omega

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
