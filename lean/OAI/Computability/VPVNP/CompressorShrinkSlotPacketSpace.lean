import OAI.Computability.VPVNP.CompressorShrinkSlotBoundary
import OAI.Computability.VPVNP.CompressorShrinkSlotWindow
import OAI.Computability.VPVNP.CompressorWindowPackets
import OAI.Computability.VPVNP.CompressorShrinkLevelSpace

/-!
# Physical address and calendar bounds for shrinking slot packets

At each repetition, the selected score and old role rows lie in table zero
and the complete slot construction fits in table three. Its exclusive end
precedes the next level header, whose incidence block receives the six copied
columns. The directory has room for every visit of the repeated block.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkSlotCalendar

open BurstRAM BlockPlanner Compression DescriptorSpace Schedule ShrinkSlots
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
variable (base : Word w) (positions blocks t : ℕ)

local notation "prog" => BlockProgram.script B
local notation "arenaL" => BlockProgram.layout B base.val positions blocks

/-- Every slot worker's actual repeated-block ordinal is strictly below
the exclusive end of the compact physical directory. -/
theorem ordinal_lt (live : t < blocks) (j : Fin (ShrinkSlotPlan.Scheduled.order.map
    (ShrinkSlotPlan.Scheduled.Stage.visit (plan B i))).length) :
    Window.ordinal (A := prog) t ((window B i).index j) < directoryRows arenaL := by
  rw [(window B i).ordinal_index, BlockProgram.directory_rows,(prog).calendar_total]
  have h := Nat.mul_le_mul_right (prog).block.length live
  rw [Nat.succ_mul] at h
  have hj := ((window B i).position j).isLt
  omega

/-- The geometry of the actual compiled allocation proves every boundary
required to preserve the planner's roots throughout a slot window. -/
theorem physical_boundary (live : t < blocks) (sites : X.positions ≤ positions)
    (room : endAddress arenaL < 2^w) :
    let old := (prog).levelsPerBlock*t+i.val
    let next := (prog).levelsPerBlock*t+(i.val+1)
    let start := tableBase arenaL old (0 : Fin 6)
    let term := ShrinkInput.termHead (w := w) X start
    let stride := (10 : Word w)
    let role := SelectedArena.roleBase X term stride
    let score := SelectedArena.origin X term stride+2
    let s := levelShape (b := S.degreeExponent i.succ) X
    let slotStart := tableBase arenaL old (3 : Fin 6)
    let slotEnd := finish s (ShrinkOutput.heads s role slotStart)
    Boundary prog arenaL base t i.val role slotStart slotEnd (incidenceStart arenaL next) score := by
  intro old next start term stride role score s slotStart slotEnd
  have nextEq : old+1 = next := by dsimp only [old,next]; omega
  have nextLive : next < (arenaL).levels := by
    have h := Nat.mul_le_mul_left (S.steps+1) live
    rw [Nat.mul_succ] at h
    have hi := i.isLt
    change (S.steps+1)*t+(i.val+1) < 1+(S.steps+1)*blocks
    omega
  have arityEq : arity (prog).catalog = (arenaL).shape.arity := rfl
  have levelFit : levelStart arenaL 0 < 2^w :=
    (levelStart_mono arenaL (Nat.zero_le (arenaL).levels)).trans_lt room
  obtain ⟨rows,pitch⟩ := Window.lowCells (A := prog) arenaL base arityEq rfl levelFit
  have rowRoom : (prog).initial.length+(t+1)*(prog).block.length ≤ directoryRows arenaL := by
    rw [BlockProgram.directory_rows,(prog).calendar_total]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ live) _
  have slotPos : 0 < slotDegree S := (Nat.two_pow_pos _).trans_le (show 2^S.degreeExponent i.castSucc ≤ slotDegree S from
    (Finset.le_sup (f := fun j : Fin (S.steps+1) ↦ 2^S.degreeExponent j) (Finset.mem_univ i.castSucc)).trans
      (le_max_right ..))
  have fieldBound : ShrinkLevelSpace.tableFactor S ≤ BlockProgram.fieldCount B := by
    unfold BlockProgram.fieldCount; omega
  have size : X.positions*ShrinkLevelSpace.tableFactor S ≤ tableWords arenaL := by
    change _ ≤ positions*slotDegree S*BlockProgram.fieldCount B
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul sites (fieldBound.trans (Nat.le_mul_of_pos_left _ slotPos))
  have ends := ShrinkLevelSpace.packed_ends S i X start start start slotStart w
  have termBound : ShrinkInput.termEnd X start 10 ≤ start+X.positions*ShrinkLevelSpace.tableFactor S := ends.2.1
  have retainedBound : SelectedFinish.stop X term stride ≤ start+X.positions*ShrinkLevelSpace.tableFactor S := ends.2.2.1
  have slotBound : slotEnd ≤ slotStart+X.positions*ShrinkLevelSpace.tableFactor S := ends.2.2.2.2.2.2
  have slotBefore : slotEnd ≤ levelStart arenaL next :=
    slotBound.trans ((Nat.add_le_add_left size _).trans (nextEq ▸ tableEnd_le_nextLevel arenaL old (3 : Fin 6)))
  have header (n : ℕ) : incidenceStart arenaL n = levelStart arenaL n+66 := rfl
  have headerBeforeTable (n : ℕ) (u : Fin 6) : incidenceStart arenaL n ≤ tableBase arenaL n u :=
    (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have nextRoom : incidenceStart arenaL next < 2^w :=
    (headerBeforeTable next 0).trans_lt (((Nat.le_add_right _ _).trans
      ((tableEnd_le_nextLevel arenaL next (0 : Fin 6)).trans (levelStart_mono arenaL nextLive))).trans_lt room)
  have oldRoom : incidenceStart arenaL old < 2^w := by
    rw [header]
    have nextFits : levelStart arenaL next+66 < 2^w := (header next) ▸ nextRoom
    have h := levelStart_mono arenaL (show old ≤ next by omega)
    omega
  have startToSlot : start+tableWords arenaL ≤ slotStart :=
    tableEnd_le_tableBase arenaL old (show (0 : Fin 6) < 3 by decide)
  have slotStartFit : slotStart < 2^w := ((Nat.le_add_right _ _).trans
    ((tableEnd_le_nextLevel arenaL old (3 : Fin 6)).trans (levelStart_mono arenaL (by omega : old+1 ≤ (arenaL).levels)))).trans_lt room
  have tr : ShrinkInput.termEnd X start 10 < 2^w :=
    termBound.trans_lt (((Nat.add_le_add_left size start).trans startToSlot).trans_lt slotStartFit)
  let N := ShrinkTermSelection.bundles X*ShrinkTermSelection.ranks (S.degreeExponent i.castSucc)
  change ShrinkInput.stop X start+2*N+N*10 < 2^w at tr
  have termAt : term.val = ShrinkInput.stop X start+2*N := Nat.mod_eq_of_lt (by omega)
  obtain ⟨h₀,h₁,h₂,h₃⟩ := ShrinkInput.range_bounds X start
  have headLow : levelStart arenaL 0 ≤ start := (levelStart_mono arenaL (Nat.zero_le old)).trans
    ((Nat.le_add_right _ _).trans (headerBeforeTable old 0))
  have scoreLow : levelStart arenaL 0 ≤ score := by
    dsimp only [score,SelectedArena.origin]
    omega
  have scoreRole : score < role := by
    dsimp only [score,role,SelectedArena.roleBase,SelectedArena.placementBase]; omega
  have roleEnd : role ≤ SelectedFinish.stop X term stride := by
    unfold SelectedFinish.stop SelectedFinish.rowStart SelectedFinish.countStart SelectedArena.endAddr; omega
  have roleBefore : role ≤ slotStart :=
    roleEnd.trans (retainedBound.trans ((Nat.add_le_add_left size start).trans startToSlot))
  exact ⟨arityEq,rfl,levelFit,rowRoom,rows,pitch,scoreLow.trans scoreRole.le,roleBefore,
    (header old) ▸ headerBeforeTable old 3,slotBefore,(header next).ge,scoreLow,scoreRole.trans_le roleBefore,
    (header old) ▸ oldRoom.le,(header next) ▸ nextRoom.le⟩

end CompressorRecords.ShrinkSlotCalendar

end

end VPVNP
end Computability
end OAI
