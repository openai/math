import OAI.Computability.BorderVNP.CubeTeamRowClockStages
import OAI.Computability.BorderVNP.CubeTeamOwnedDiagonalDispatch
import OAI.Computability.BorderVNP.CubeTeamOwnedRole

/-! # Charging the row programs at their actual dispatch keys

The quotient and remainder of the native counter select an ordered endpoint
view. Its physical role allowance is exactly the sum used by the scatter,
vertex emission and declaration check on that side. The same keys occur in
the linear team clock and in its sum over ordered symbol pairs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.OwnedStages Physical Scatter Padding.Banks TeamRowSources TeamRowClock

variable {n d blocks b h K s : ℕ}

/-- Physical role allowance for the native outer row cursor, with zero outside
the allocated table of ordered pairs. -/
def physicalCostAt (l : TeamRowPrepare.Layout) (blocks b h K s : ℕ) (axis : Fin (n+1)) (q : ℕ) :=
  roleAt (physicalRoleTicks blocks b h K s axis : Fin l.d → Fin l.d → ℕ) q

/-- A valid outer cursor retrieves the two symbols of its finite product index. -/
theorem physicalCostAt_pair (l : TeamRowPrepare.Layout) (blocks b h K s : ℕ) (axis : Fin (n+1))
    (q : Fin (l.d*l.d)) :
    physicalCostAt l blocks b h K s axis q.val =
      physicalRoleTicks blocks b h K s axis (pairAt l.d q).1 (pairAt l.d q).2 := by
  simp only [physicalCostAt,roleAt,dite_eq_left q.isLt,Fin.eta,pairAt]

/-- The key of an oriented pair addresses its exact charged role. -/
theorem physicalCostAt_key (l : TeamRowPrepare.Layout) (blocks b h K s : ℕ) (axis : Fin (n+1))
    (alphabet : l.d = d) (p : Fin d × Fin d) :
    physicalCostAt l blocks b h K s axis (key p) = physicalRoleTicks blocks b h K s axis p.1 p.2 := by
  subst d
  exact roleAt_pair _ p.1 p.2

private theorem strict_check (i : Fin (n+1)) (pair : Symbols d) :
    strictCheckTicks i pair blocks b h K s = LocalRow.strictTicks n b h K s blocks i pair := by
  simp only [strictCheckTicks,LocalRow.strictTicks,show LocalRow.finish.slots = 5 from rfl,Nat.add_assoc]

private theorem diagonal_check (i : Fin (n+1)) (g : Fin d) :
    diagonalCheckTicks i g blocks b h K s = LocalRow.diagonalTicks n b h K s blocks i g := by
  simp only [diagonalCheckTicks,LocalRow.diagonalTicks,show LocalRow.finish.slots = 5 from rfl,Nat.add_assoc]

/-- Both possible endpoint orders of a strict row charge the physical packet,
the two singleton orientations, the directory pass and the strict checker. -/
theorem strictRole_ticks (D : PacketRowData n d blocks b h K s) (S : SideData n d blocks b h) :
    physicalRoleTicks blocks b h K s D.axis (oriented D.pair D.high).1 (oriented D.pair D.high).2 =
      sideCost D S + LocalRow.strictTicks n b h K s blocks D.axis D.pair := by
  let first := D.singletonRow D.pair.val.1 D.pair.val.2 S.bank 0 0 S.value
  let second := D.singletonRow D.pair.val.2 D.pair.val.1 S.bank 0 0 S.value
  have cost := strict_stage_cost (K := K) (s := s) D.axis D.pair first second
    ⟨rfl,rfl⟩ ⟨rfl,rfl⟩ ⟨rfl,rfl⟩
  dsimp only at cost
  rw [strict_check] at cost
  cases high : D.high
  · exact cost.1
  · exact cost.2

/-- On the actual directed key, the physical cost equals the allowance of
`strictRole_run` for the real packet and singleton bank data. -/
theorem physicalCostAt_strict (l : TeamRowPrepare.Layout) (A : Data n d blocks b h K s)
    (alphabet : l.d = d) (pair : Symbols d) (high : Bool) (sel cross power header out : ℕ) :
    physicalCostAt l blocks b h K s A.axis (key (oriented pair high)) =
      sideCost (A.packet pair high sel cross) (A.side power header out) +
        LocalRow.strictTicks n b h K s blocks A.axis pair := by
  rw [physicalCostAt_key l blocks b h K s A.axis alphabet]
  exact strictRole_ticks (A.packet pair high sel cross) (A.side power header out)

/-- A repeated-symbol dispatch key pays exactly one singleton pass and the
actual diagonal declaration checker. -/
theorem physicalCostAt_diagonal (l : TeamRowPrepare.Layout) (A : Data n d blocks b h K s)
    (alphabet : l.d = d) (g : Fin d) (sel cross : ℕ) :
    physicalCostAt l blocks b h K s A.axis (key (g,g)) =
      singleStageCost (A.single g g sel cross) + LocalRow.diagonalTicks n b h K s blocks A.axis g := by
  rw [physicalCostAt_key l blocks b h K s A.axis alphabet,← diagonal_check]
  exact diagonal_stage_cost _ _ _ rfl rfl rfl

/-- The linear native scan charges each role exactly when the physical owner
table assigns its first symbol to the team. Setup and the final guard occur once. -/
theorem ticks_physicalCostAt (l : TeamRowPrepare.Layout) (owner : ℕ → ℕ)
    (blocks b h K s : ℕ) (axis : Fin (n+1)) :
    ticks l owner (physicalCostAt l blocks b h K s axis) =
      TeamRowPrepare.setup.slots + teamClock (fun u : Fin l.d => owner u.val) l.teamID
        (TeamRowPrepare.prepare.slots+5) (physicalRoleTicks blocks b h K s axis) + 1 := by
  rw [ticks,linear_teamClock]
  simp only [physicalCostAt,roleAt_pair]

/-- Changing from the dispatch alphabet to the schedule's equal alphabet gives
the exact clock used by `checkedTeamTicks_le_sq` and its eventual exterior bound. -/
theorem ticks_at_scheduled_alphabet (l : TeamRowPrepare.Layout) (owner : ℕ → ℕ)
    (blocks b h K s : ℕ) (axis : Fin (n+1)) (alphabet : l.d = d) :
    ticks l owner (physicalCostAt l blocks b h K s axis) =
      ticks l owner (roleAt (physicalRoleTicks blocks b h K s axis : Fin d → Fin d → ℕ)) := by
  subst d
  rfl

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
