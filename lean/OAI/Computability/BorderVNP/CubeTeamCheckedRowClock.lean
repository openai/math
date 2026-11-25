import OAI.Computability.BorderVNP.CubeTeamNativeRowClock
import OAI.Computability.BorderVNP.CubeISAOwnedRowSetupPacket
import OAI.Computability.BorderVNP.CubeISALocalRowCode
import OAI.Computability.BorderVNP.CubeTeamBudgetGuard

/-! # Fixed-format bound on the native checked row clock -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowClock

open RoutingISA Physical

variable {n d : ℕ}

/-- The strict scatter and vertex passes each prepare the packet frame. Both
singleton orientations load their frame and perform the two three-tick swaps. -/
def strictSetupSlots (n b h K s : ℕ) :=
  2*(OwnedRowSetup.packet n b h K s).slots + 2*OwnedRowSetup.single.slots + 6

/-- Fixed allowance for scatter, directory and local tally setup plus the two final
guards of the clear and comparison loops and the strict tally's final register swap. -/
def roleFixed (n b h K s : ℕ) (tallySetup tallyFinish : Code) :=
  strictSetupSlots n b h K s + tallySetup.slots + tallyFinish.slots + 5

/-- Four ticks to clear a coordinate, then the actual comparison body and its guard. -/
def coordinateTicks := 4+(CubeLengths.rowBody.slots+1)

/-- Each scanned coordinate costs thirteen ticks across initialization and comparison. -/
theorem coordinateTicks_eq : coordinateTicks = 13 := by decide

/-- The per-role native clock with its separate strict/diagonal setups, all three
candidate loops, zeroing of the local tallies and the final comparison. -/
def checkedRoleTicks (blocks b h K s : ℕ) (tallySetup tallyFinish : Code) (i : Fin (n+1)) (u v : Fin d) :=
  (if u = v then OwnedRowSetup.single.slots else strictSetupSlots n b h K s) +
    tallySetup.slots + (4*(n+1)+1) + tallyFinish.slots + ((n+1)*(CubeLengths.rowBody.slots+1)+1) +
    (if u = v then 0 else 3) + scatterRoleTicks blocks b h K s i u v + tallyTicks blocks b h K i u v +
    vertexTicks n d blocks K h u v

/-- The strict preparation cost bounds both roles, including the single diagonal orientation. -/
theorem checkedRoleTicks_le (blocks b h K s : ℕ) (tallySetup tallyFinish : Code) (i : Fin (n+1)) (u v : Fin d) :
    checkedRoleTicks blocks b h K s tallySetup tallyFinish i u v ≤
      nativeRoleTicks blocks b h K s (roleFixed n b h K s tallySetup tallyFinish) coordinateTicks i u v := by
  have fixed : (if u = v then OwnedRowSetup.single.slots else strictSetupSlots n b h K s) ≤
      strictSetupSlots n b h K s := by
    split_ifs <;> simp only [strictSetupSlots] <;> omega
  have swap : (if u = v then 0 else 3) ≤ 3 := by split_ifs <;> decide
  simp only [checkedRoleTicks,nativeRoleTicks,roleFixed,coordinateTicks,Nat.mul_add,Nat.mul_comm 4 (n+1)]
  omega

/-- Coefficient in the team clock. Every quantity in it is fixed once the packet
format and tally setup instructions are fixed, independently of the label count and padding. -/
def formatCoefficient (n b h K s : ℕ) (tallySetup tallyFinish : Code) :=
  TeamRowPrepare.setup.slots+1 + TeamRowPrepare.prepare.slots+5 +
    nativeProbe n K h (roleFixed n b h K s tallySetup tallyFinish) coordinateTicks +
    1000000*nativeBit n b h K s

private theorem absorb_clock (setup Q V Z X : ℕ) (positive : 0 < Z) :
    setup+(Q*Z+V*(1000000*X/256))+1 ≤ (setup+1+Q+1000000*V)*(Z+X) := by
  have init := Nat.le_mul_of_pos_right (setup+1) positive
  have raw := Nat.mul_le_mul_left V (Nat.div_le_self (1000000*X) 256)
  have rearrange : (setup+1+Q+1000000*V)*(Z+X) = (setup+1)*Z + Q*Z + V*(1000000*X) +
      ((setup+1)*X+Q*X+(1000000*V)*Z) := by ring
  rw [rearrange]
  omega

/-- For a passing physical schedule, the team clock is at most a format-dependent
multiple of `Z⁴+X₀`. The owner queries, row cost and both capacity comparisons are
those used by the native programs. -/
theorem checkedTeamTicks_le {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
    {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups} {A : Type*} [Fintype A]
    {label : Fin l.cells → Label (n+1) l.groups} {recv : A → Fin l.cells} {w : A → ℕ}
    (result : GroupWeights.ScheduleResult l teams orig mem)
    (image : GroupWeights.PhysicalImage l orig blocks b K h D label recv w)
    (team : Fin (teams.r+1)) (dispatch : TeamRowPrepare.Layout) (hd : dispatch.d = l.groups)
    (ht : dispatch.teamID = team.val) (X s : ℕ) (tallySetup tallyFinish : Code)
    (positive : 0 < h*b) (groups : 0 < l.groups)
    (pass : (TeamBudget.Layout.mk (teams.r+1) X teams.totals).Passes mem) :
    TeamRows.ticks dispatch (fun u => mem (teams.owners+u))
      (roleAt (checkedRoleTicks blocks b h K s tallySetup tallyFinish D.1 : Fin l.groups → Fin l.groups → ℕ)) ≤
      formatCoefficient n b h K s tallySetup tallyFinish*((l.groups^(n+1))^4+X) := by
  let F := roleFixed n b h K s tallySetup tallyFinish
  let U := TeamRowPrepare.setup.slots+1
  let Q := TeamRowPrepare.prepare.slots+5+nativeProbe n K h F coordinateTicks
  let V := nativeBit n b h K s
  let Z := (l.groups^(n+1))^4
  have cap := (TeamBudget.Layout.le_teamLimit ⟨teams.r+1,X,teams.totals⟩ _).1 (pass.1 team.val team.isLt)
  have run := nativeTeamTicks_le result image team dispatch hd ht X s F coordinateTicks _ positive
    (fun u v => (roleAt_pair _ u v).le.trans (checkedRoleTicks_le blocks b h K s tallySetup tallyFinish D.1 u v)) cap
  apply run.trans
  have cEq : formatCoefficient n b h K s tallySetup tallyFinish = U+Q+1000000*V := by
    dsimp only [formatCoefficient,F,U,Q,V]
    omega
  rw [cEq]
  exact absorb_clock TeamRowPrepare.setup.slots Q V Z X (pow_pos (pow_pos groups _) _)

/-- The role cost of the actual local checker, including its strict-only register swap. -/
def physicalRoleTicks (blocks b h K s : ℕ) (i : Fin (n+1)) (u v : Fin d) :=
  checkedRoleTicks blocks b h K s (LocalRow.setup n b h K s) LocalRow.finish i u v

/-- The actual packet and tally instruction tables determine a single constant. -/
def physicalCoefficient (n b h K s : ℕ) :=
  formatCoefficient n b h K s (LocalRow.setup n b h K s) LocalRow.finish

/-- Counting only the two unfixed label tails gives the stronger native bound
`formatCoefficient*(Z²+X₀)` for the physically assembled scatter, check and directory loops. -/
theorem checkedTeamTicks_le_sq {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
    {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups} {A : Type*} [Fintype A]
    {label : Fin l.cells → Label (n+1) l.groups} {recv : A → Fin l.cells} {w : A → ℕ}
    (result : GroupWeights.ScheduleResult l teams orig mem)
    (image : GroupWeights.PhysicalImage l orig blocks b K h D label recv w)
    (team : Fin (teams.r+1)) (dispatch : TeamRowPrepare.Layout) (hd : dispatch.d = l.groups)
    (ht : dispatch.teamID = team.val) (X s : ℕ) (positive : 0 < h*b) (groups : 0 < l.groups)
    (pass : (TeamBudget.Layout.mk (teams.r+1) X teams.totals).Passes mem) :
    TeamRows.ticks dispatch (fun u => mem (teams.owners+u))
      (roleAt (physicalRoleTicks blocks b h K s D.1 : Fin l.groups → Fin l.groups → ℕ)) ≤
      physicalCoefficient n b h K s*((l.groups^(n+1))^2+X) := by
  let U := TeamRowPrepare.setup.slots
  let overhead := TeamRowPrepare.prepare.slots+5
  let F := roleFixed n b h K s (LocalRow.setup n b h K s) LocalRow.finish
  let Q := nativeProbe n K h F coordinateTicks
  let V := nativeBit n b h K s
  let Z := (l.groups^(n+1))^2
  let role : Fin l.groups → Fin l.groups → ℕ := physicalRoleTicks blocks b h K s D.1
  let owner (u : Fin l.groups) := mem (teams.owners+u.val)
  have rows (u v : Fin l.groups) : role u v ≤ Q*(l.groups^n)^2+V*rowRaw blocks (h*b) D.1 u v :=
    (checkedRoleTicks_le blocks b h K s _ _ D.1 u v).trans (nativeRoleTicks_le_trials _ _ _ _ _ _ _ _ u v positive)
  have clock := teamClock_le_sq blocks (h*b) D.1 owner team.val overhead Q V role rows
  have raw : ownedRaw owner team.val (blocks*(h*b)) D.1 ≤ 1000000*X/256 :=
    (ownedRaw_le_stored result image team).trans (pass.1 team.val team.isLt)
  have clock' := clock.trans (Nat.add_le_add_left (Nat.mul_le_mul_left V raw) _)
  have coeff : physicalCoefficient n b h K s = U+1+(overhead+Q)+1000000*V := by
    dsimp only [physicalCoefficient,formatCoefficient,U,overhead,Q,F,V]
    omega
  rw [TeamRows.ticks,hd,ht,linear_teamClock l.groups (fun u => mem (teams.owners+u)) (roleAt role) team.val overhead]
  simp only [roleAt_pair]
  rw [coeff]
  exact (Nat.add_le_add_right (Nat.add_le_add_left clock' U) 1).trans
    (absorb_clock U (overhead+Q) V Z X (pow_pos (pow_pos groups _) _))

end Cube.TeamRowClock

end BorderVNP
end Computability
end OAI
