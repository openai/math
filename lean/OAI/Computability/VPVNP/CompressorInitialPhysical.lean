import OAI.Computability.VPVNP.CompressorInitialOnline
import OAI.Computability.VPVNP.CompressorInitialConverse

/-!
# The actual initial cursor prefix of the finite pair-ABI descriptor program

The startup bank identifies the ready calendar. The four fixed initial
phases run as a deterministic prefix on every accepting Fin11 branch.
At zero blocks the closing calendar call accepts and determines the
whole native choice string and report log.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.InitialPhysical

open BurstRAM Compression DescriptorSpace BlockPlanner Schedule BranchSegments SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable (base positions blocks cap b l width n : ℕ) (pub : Fin 11 → Word w) (m : Memory w)
local notation "A" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base positions blocks
local notation "a" => S.degreeExponent 0
local notation "pt" => Workspace.ports (arity (Script.catalog (BlockProgram.script B))) (pub 2)
local notation "P" => OnlineWorkspace.program (Script.plan (BlockProgram.script B)) pub

private theorem count_lt (fit : endAddress L < 2^w) : directoryRows L < 2^w := by
  have head : levelStart L 0 < 2^w := (levelStart_mono L (Nat.zero_le _)).trans_lt fit
  have hr : directoryRows L ≤ directoryRows L*((L).shape.arity+3) :=
    Nat.le_mul_of_pos_right _ (by omega)
  change directoryBase L + directoryRows L*((L).shape.arity+3) + 0*levelWords L < 2^w at head
  omega

/-- Every successful run through the native four visits has the source
effects at all data addresses. At zero blocks the same initial segment
followed by the terminal calendar call is the unique accepting run. -/
theorem run (X : State a l) (fit : endAddress L < 2^w) (workspace : (pub 2).val = base)
    (ready : OnlineWorkspace.Ready (A).size (L).shape.arity (pub 2) (directoryRows L) (levelWords L) m)
    (cursor : BlockStartupPrefix.Resident L a b l width n (pub 2) m X)
    (clock : InitialScriptPackets.budget A (BlockProgram.layout B 0 0 0) a ≤ cap)
    (bounds : Online.Run.ControlBounds (A).plan cap (w := w)) :
    ∃ cut : Cut P (cap+24) (some 0) m Unit,
      (cut.part ()).state = some 0 ∧
      Agree (levelStart L 0 ≤ ·) (BlockInitialPackets.post L a b l width m) (cut.part ()).memory ∧
      ((cut.part ()).memory (pt).ordinal.val).val = 4 ∧
      (cut.part ()).memory (pt).rows.val = m (pt).rows.val ∧
      (cut.part ()).memory ((pt).directory-1).val = m ((pt).directory-1).val ∧
      Workspace.Installed (arity (A).catalog) (pub 2) (cut.part ()).memory ∧
      (blocks = 0 → ∃ bs logs, runSegment P (cap+24) (some 0) m bs = some logs ∧
        endState (some 0) logs = none ∧ ∀ other rs,
          runSegment P (cap+24) (some 0) m other = some rs → endState (some 0) rs = none →
            other = bs ∧ rs = logs) := by
  let script := BlockProgram.script B
  let alloc := BlockProgram.layout B base positions blocks
  have hg : arity script.catalog = alloc.shape.arity := rfl
  have hp : 0 < alloc.levels := by change 0 < 1+(S.steps+1)*blocks; omega
  have rows : directoryRows alloc = 4+blocks*script.block.length :=
    (BlockProgram.directory_rows B base positions blocks).trans (script.calendar_total blocks)
  have tagged : m (pt).tag.val = LiveStageLink.tagWord w (Online.calendarIndex script.size script.size) := by
    change m (pt).tag.val = ((script.size+1+0 : ℕ) : Word w)
    rw [Nat.add_zero]
    exact ready.tag
  have count : (m (pt).rows.val).val = directoryRows alloc := by
    rw [show m (pt).rows.val = (directoryRows alloc : Word w) from ready.count]
    exact Nat.mod_eq_of_lt (count_lt B base positions blocks fit)
  have capFit : InitialScriptPackets.budget script alloc a ≤ cap :=
    (InitialScriptPackets.budget_fixed B base positions blocks a) ▸ clock
  obtain ⟨steps,actual,_,trace,agree,ordinal,total,pitch,stable⟩ := InitialOnline.interval script alloc (pub 2)
    a b l width cap capFit hg workspace hp (by change 14 ≤ 54; decide) fit (InitialScriptPackets.actual_order B base positions blocks)
    m cursor.walk (by omega) ready.ordinal count tagged ready.pitch
  let inner := Online.Run.intervalSegment script.plan pt (state := 0) bounds tagged steps actual
  let c := InitialConverse.cut script pub alloc a b l width cap m steps bounds tagged ready.bank actual stable trace
  have state : (c.part ()).state = some 0 :=
    (OnlineWorkspace.framedSegment_state script.plan pub inner (stable.banks ready.bank)).trans
      (Online.Run.interval_state_zero script.plan pt bounds tagged steps actual)
  have mem : (c.part ()).memory = Online.Run.finalMemory (C := script.catalog) pt m steps :=
    (OnlineWorkspace.framedSegment_memory script.plan pub inner (stable.banks ready.bank)).trans
      (Online.Run.interval_memory script.plan pt (state := 0) bounds tagged steps actual)
  refine ⟨c,state,mem.symm ▸ agree,mem.symm ▸ ordinal,mem.symm ▸ total,mem.symm ▸ pitch,?_,?_⟩
  · have h := stable.installed ready.bank (Online.Run.intervalLog script.plan pt m steps).length
    rw [List.take_length] at h
    change Workspace.Installed (arity script.catalog) (pub 2) inner.memory at h
    exact (OnlineWorkspace.framedSegment_memory script.plan pub inner (stable.banks ready.bank)).symm ▸ h
  · intro zero
    have closed : let endMem := Online.Run.finalMemory (C := script.catalog) pt m steps
      endMem (pt).rows.val ≤ endMem (pt).ordinal.val := by
      apply Fin.le_def.mpr
      rw [total,count,ordinal,rows,zero,Nat.zero_mul,Nat.add_zero]
    exact ⟨_,_,InitialConverse.exhausted script pub alloc a b l width cap m steps bounds tagged ready.bank
      actual stable trace closed⟩

end CompressorRecords.InitialPhysical

end VPVNP
end Computability
end OAI
