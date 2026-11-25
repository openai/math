import OAI.Hierarchy.TraceReceiverCommandHeader
import OAI.Hierarchy.TraceResourceMount
import OAI.Hierarchy.TraceReceiverMapsRun

namespace OAI
/-! # Executing every terminal writer on the restored ordered root list -/
noncomputable section
namespace Hierarchy.TraceReceiverProgram
open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open TickTerminalRoot TraceFactorReceiver TraceReceiverTasks
open scoped Fin.CommRing BigOperators Classical

variable {W : ℕ} (D : TraceReceiverTasks.Layout) (A : Arena) (count cap header commands cursor : ℕ)
    (width : Fin 3→ℕ) (dst len : ℕ→ℕ) (n : ℕ) (m : Memory W)
set_option quotPrecheck false
local notation "parent" => TraceAdmission.Resources.mounted D.parent [A.metadata,A.physicalPins,0,0] m
local notation "made" => beforeImage D count cap width n parent
local notation "images" => mapImages A D.tasks header dst len made
local notation "ranged" => rangeImage D.current count commands 0 7 (images n)
local notation "ctr" => (countdown (W:=W) A).val

def terminalOutput : Memory W := Issued.image cursor commands D.tasks n ranged

def mapClock : ℕ := 4+7*n+∑ j ∈ Finset.range n,let i:=n-(j+1)
  mapStepCost A D.tasks header (len i) (images i)

def terminalClock : ℕ := 13+(before_clock n+(
  mapClock D A count cap header width dst len n m+
  (4096+((13+7224*n)+(4+2*(2*(Cursor.term W cursor commands count).binds+4))))))

/-- Physical observations consumed by the native program. The per-root
bounds and kept counter concern the actual countdown states; none of the
observations specifies a prewritten final forest or inferred evaluation. -/
structure TerminalWriterRoom : Prop where
  beforeBounds : BeforeBounds D count cap width n W
  countWord : (parent count).val=n
  caches : ∀ j (i : Fin n),(amountAddress D.selected D.first D.results j parent (i.val:Word W)).val<D.current
  initial : (made ctr).val=n
  root : ∀ i<n, MapBounds A D.tasks header (dst i) (len i) (images i)
  outside : ctr<header ∨ header+3≤ctr
  saved : ∀ i<n,ctr<dst i ∨ dst i+len i≤ctr
  kept : ∀ i<n,KeptByRoot A (mapSeed A D.tasks header (images i)) ctr
  currentRoom : D.current+7<2^W
  cursorRoom : cursor+2<2^W
  countRoom : count<2^W
  countHead : count<D.current ∨ D.current+7≤count
  countCursor : count<cursor ∨ cursor+2≤count
  countCommands : count<commands ∨ commands+7*n≤count
  finalCount : images n count=(n:Word W)
  commandRoom : commands+7*n<2^W
  commands : Commands.Separate D.tasks commands n ranged

theorem terminal_writes (room : TerminalWriterRoom D A count cap header commands cursor width dst len n m) :
    ((TraceAdmission.Resources.mount W D.parent [A.metadata,A.physicalPins,0,0]).seq
      ((before W D count cap width).seq ((maps W A D.tasks header).seq
        ((rangeSeed W D.current count commands 0 7).seq
          ((Commands.procedure W D.current commands D.tasks).seq (Cursor.program W cursor commands count)))))).Spec
      (·=m) (fun _ out=>out=terminalOutput D A count cap header commands cursor width dst len n m)
      (terminalClock D A count cap header commands cursor width dst len n m) := by
  intro _ _ _ machine
  refine Issued.followed _ _ m parent _ _ _ ?_ ?_ machine
  · intro pp rr kk M pc reg pub exit installed data cfg start here hm
    subst start
    exact TraceAdmission.Resources.mount_spec D.parent [A.metadata,A.physicalPins,0,0] M pc reg pub exit
      installed data cfg m here trivial
  · intro _ _ _ machine
    refine Issued.followed _ _ parent made _ _ _ ?_ ?_ machine
    · intro _ _ _ M
      exact before_run D count cap width n parent room.beforeBounds room.countWord room.caches M
    · intro _ _ _ machine
      refine Issued.followed _ _ made (images n) _ _ _ ?_ ?_ machine
      · intro _ _ _ M
        exact maps_run A D.tasks header dst len made n room.initial room.root room.outside room.saved room.kept M
      · intro _ _ _ M
        exact Issued.tail_run D.current cursor commands D.tasks count n (images n) room.currentRoom
          room.cursorRoom room.countRoom room.countHead room.countCursor room.countCommands room.finalCount
          room.commandRoom room.commands M

end Hierarchy.TraceReceiverProgram
end

end OAI
