import OAI.Hierarchy.DescentIssuedSnapshotRanks
import OAI.Hierarchy.DescentRegisteredPrefixRooms

namespace OAI
/-! # Public snapshot addresses selected by the physical reset and their count-capture frame -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.AtPorts
open ProtocolRAM
noncomputable section

/-- The forward-rank array written by the reset's actor census. -/
def snapshotDirectory (a : AtPorts) : Bank :=
  let date:=a.inner
  let base:=date.rebased (date.stageStart a.priorStart)
  date.successor.actor.directory (date.successor.middle.stop base) |>.ranks

theorem snapshotDirectory_after (a : AtPorts) : a.floor≤a.snapshotDirectory.base := by
  let d:=a.inner
  let x:=d.stageStart a.priorStart
  let b:=d.rebased x
  let f:=d.successor.middle.stop b
  let actor:=d.successor.actor
  have enter : a.priorStart≤x := d.ingress.after _
  have stages:=d.occupied x
  have middle : b≤f := by
    dsimp only [f]
    rw [d.successor.middle.translated]
    omega
  have move:=actor.translated f
  change actor.endAddress f+(actor.directory 0).size=f+(actor.endAddress 0+(actor.directory 0).size) at move
  change a.floor≤actor.endAddress f+2*(actor.directory f).pitch
  have head := a.stages.1
  change x≤(d.chart x).endAddress ∧ (d.chart x).endAddress≤b ∧ _ at stages
  omega
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.AtPorts

namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentCompiler DescentExteriorReplay ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist len w : ℕ} {q ε : ℝ}
    {D n₀ h C f g cut tail : ℕ} (ctl : ResetRates G S k D n₀ h C f g cut tail)

omit [Fintype P] in
theorem snapshotCalendar_on_event {t : RunTrace G q ε S k wire hist len bits d}
    (kinds : List Bool) (factors : List ℕ) (directory : ℕ→Bank)
    (tags : t.path.kinds=kinds) (i : ℕ) (e : t.path.Event i) :
    (SnapshotCalendar ctl kinds factors directory).compact i=if e.isReset then some (directory i) else none := by
  change (if (kinds.drop i).head?.getD false then some (directory i) else none)=_
  have same := e.shown
  rw [tags] at same
  rw [same]
  rfl

namespace RegisterTimeline
variable {Choice : Type*} (traces : Choice→RunTrace G q ε S k wire hist len bits d)
    {n degree : ℕ} (menu : Menu n degree) (first : Position)
local notation "cursor" => calendar (w:=w) traces menu first
local notation "cpu" => instruction (w:=w) traces menu first
local notation "steps" => issued (w:=w) traces menu

/-- This address depends only on the selected public program at earlier dates. -/
def snapshotDirectory (i : ℕ) : Bank :=
  (PhysicalReset.scheduledAtPorts G S menu.board k menu.tail i menu.p menu.f menu.gain menu.drift
    menu.degreeLimit menu.payload menu.ordinary menu.op (S.firstWidth G.b menu.p)
    (S.grainAt G.b menu.p 0) (cursor i).ports (cursor i).floor).snapshotDirectory

local notation "dir" => snapshotDirectory (w:=w) traces menu first
local notation "A" => SnapshotCalendar ctl (kindCalendar S.rounds S.height)
    (capCalendar G.b S.rounds g S.height) dir

omit [Fintype P] in
theorem snapshotDirectory_after_first (i : ℕ) : first.floor≤(dir i).base := by
  have live : ∀j,first.floor≤(cursor j).floor := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact ih.trans (selected_floor steps j (cursor j))
  exact (live i).trans (PhysicalReset.AtPorts.snapshotDirectory_after
    (PhysicalReset.scheduledAtPorts G S menu.board k menu.tail i menu.p menu.f menu.gain menu.drift
      menu.degreeLimit menu.payload menu.ordinary menu.op (S.firstWidth G.b menu.p)
      (S.grainAt G.b menu.p 0) (cursor i).ports (cursor i).floor))

omit [Fintype P] in
theorem snapshotCalendar_above (i : ℕ) (r : Bank) (slot : (A).compact i=some r) :
    first.floor≤r.base := by
  change (if ((kindCalendar S.rounds S.height).drop i).head?.getD false then some (dir i) else none)=some r at slot
  split at slot
  · cases slot
    exact snapshotDirectory_after_first traces menu first i
  · cases slot

variable (c : Choice) (m : Memory w)
local notation "t" => traces c
local notation "mem" => DateCode.history cpu m
local notation "family" => RunTrace.machine traces (fun i _=>cpu i)
variable (kinds : (traces c).path.kinds=kindCalendar S.rounds S.height)
    (well : ∀i,Protected (instruction (w:=w) traces menu first i) (calendar (w:=w) traces menu first i).floor menu.header) (header : menu.header<first.floor)
    (resetRows : ∀i (e : (traces c).path.Event i), e.isReset=true →
      e.rankPublication (snapshotDirectory (w:=w) traces menu first i) (calendar (w:=w) traces menu first (i+1)).floor
        (DateCode.history (instruction (w:=w) traces menu first) m (i+1)))

include kinds well header resetRows in
omit [Fintype P] in
theorem registered_snapshot_ranks : (t).path.snapshotRanks A (cursor len).floor (DateCode.history family m len) := by
  apply issued_snapshot_ranks traces menu first c m A dir well
  · intro i r slot
    exact header.trans_le (snapshotCalendar_above ctl traces menu first i r slot)
  · exact snapshotCalendar_on_event ctl _ _ dir kinds
  · intro i e
    cases e with
    | ordinary => trivial
    | reset before batch suffix joined => exact resetRows i (.reset before batch suffix joined) rfl

include kinds well header in
omit [Fintype P] in
/-- Identify a reset's publication with the chosen instruction, including the
actual return floor. The given publication uses only this one issued move. -/
theorem registered_snapshot_rows_of_moves
    (fixed : ∀i (l r : RunTrace.Events traces i) (x y : Move w),
      steps i l (cursor i) x→steps i r (cursor i) y→x=y)
    (onReset : ∀i(e : (t).path.Event i),e.isReset=true→∃ mv : Move w,
      steps i ⟨c,e⟩ (cursor i) mv ∧ e.rankPublication (dir i) mv.next.floor (mv.code.nextMemory (mem i))) :
    (t).path.snapshotRanks A (cursor len).floor (DateCode.history family m len) := by
  apply registered_snapshot_ranks ctl traces menu first c m kinds well header
  intro i e tag
  obtain ⟨mv,hit,newRank⟩:=onReset i e tag
  obtain ⟨issuedCode,issuedCursor⟩:=returned traces menu first i ⟨c,e⟩ mv hit
    (fun r y arrived=>fixed i r ⟨c,e⟩ y mv arrived hit)
  change e.rankPublication (dir i) (cursor (i+1)).floor ((cpu i).nextMemory (mem i))
  rw [issuedCode,issuedCursor]
  exact newRank

include kinds well header resetRows in
omit [Fintype P] in
theorem captured_snapshot_ranks (firstCount countRows replayBase : ℕ) (source : ℕ→ℕ)
    (low : firstCount+countRows≤first.floor) (end_ : (cursor len).floor≤replayBase) :
    (t).path.snapshotRanks A replayBase
      (DescentLowCountBook.output firstCount source (DateCode.history family m len) countRows) := by
  apply (t).path.snapshotRanks_count_capture A source
    (registered_snapshot_ranks ctl traces menu first c m kinds well header resetRows) end_
  intro i _ bank slot
  exact Or.inr (low.trans (snapshotCalendar_above ctl traces menu first i bank slot))

end RegisterTimeline
end
end Hierarchy.DescentSixParty.Chronology

end OAI
