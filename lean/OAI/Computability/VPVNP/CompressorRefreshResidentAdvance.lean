import OAI.Computability.VPVNP.CompressorRefreshPayloadCapture
import OAI.Computability.VPVNP.CompressorCompiledResident
import OAI.Computability.VPVNP.CompressorSelectedPayloadFrames

/-!
# Advancing the resident history through a selected refresh

The header substep publishes the successor scalars and pointers. The native
core, copies and placement fill the graph, directory and selected payload.
Their shared output is the resident memory for the next pass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RefreshPayloadHistory

open BurstRAM BlockPlanner BlockHeaderRun Compression DescriptorSpace PortRefresh
open SourceOnline SelectedPayloadHistory SelectedDirectoryHistory
open PairSimulation.TraversalRoles
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
variable {g w : ℕ} (base : Word w) (positions blocks t : ℕ)
variable (f : B.Entry → R) (hf : B.IsSolution f) (X : State S.portExponent (S.portExponent+g))
variable (c : Refresh.DyadicRefreshChoice (a₀ := S.degreeExponent 0) (g := g) X S.graph
  (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool)

local notation "lev" => RefreshPlacement.selectedLevel B f hf X c sel
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "cur" => Script.levelsPerBlock scr*t+S.steps
local notation "nxt" => cur+1
local notation "head" => levelStart L cur
local notation "nextHead" => levelStart L nxt
local notation "start" => arrayBase L cur
local notation "Y" => Refresh.dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
  (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh S.port_order (And.right S.degree_bounds) c

set_option maxHeartbeats 1600000 in
/-- Append the selected refresh to the physical directory, current graph
and payload snapshots, using the reports from all seven groups. -/
theorem advance {cap termCap n : ℕ} {initial : TaggedLayer} {initialFrame : Fin 8 → Word w}
    {past : List (SelectedLevel B f hf)} {before m : Memory w} {core copy : List (Report w)}
    {tail : List (Packet scr w)} (old new : Fin (L).levels)
    (oldAt : old.val = cur) (newAt : new.val = nxt) (index : past.length = cur)
    (live : t < blocks) (size : X.positions ≤ positions) (room : endAddress L < 2^w)
    (stored : CompiledResident.resident B f hf base positions blocks n initial initialFrame past X before)
    (sub : Substep lev L old new (by change 6 ≤ 54; decide) before)
    (headerMemory : m = finalMemory lev L old new before)
    (oldRep : (packedIncidence L w cur (lev).oldSlots).Represents X m)
    (newBank : TraversalHeaders.HeadBank L nxt (lev).outputSlots m)
    (built : RefreshCore.Built B base positions blocks t X c termCap m core)
    (copied : RefreshCopyPackets.Copied B base positions blocks t X c (after m (eventLog core)) copy)
    (installed : RefreshPlacement.TailResult B base positions blocks t cap f hf X c sel
      (after (after m (eventLog core)) (eventLog copy)) tail) :
    CompiledResident.resident B f hf base positions blocks n initial initialFrame
      (past++[lev]) ((lev).pass.next (lev).term) (post (after (after m (eventLog core)) (eventLog copy)) tail) := by
  let mid := after (after m (eventLog core)) (eventLog copy)
  let out := post mid tail
  have adj : old.val+1 = new.val := by omega
  have space := Space.ofLayout B base positions blocks t X live size room
  have hdr := space.header_before
  have high := space.array_before
  have placeEnd := space.placement_before
  have nextInc : incidenceStart L nxt = nextHead+66 := rfl
  have lowFirst : levelStart L 0+29 < head := by
    have firstLevel : 1 ≤ cur := by have := S.steps_pos; omega
    have span : levelStart L 0+29 < levelStart L 1 := by
      change levelsBase L + 0*levelWords L + 29 < levelsBase L + 1*levelWords L
      have width : 29 < levelWords L := by change 29 < 66 + _ + _; omega
      omega
    exact span.trans_le (levelStart_mono L firstLevel)
  have coreFrame := core_copy_frame B base positions blocks t X c space built copied
  have len : m (levelStart L 0+29) = (n : Word w) := by
    rw [headerMemory,sub.firstScalarTail lev adj 29 (by decide) (by change 29 < 54; decide)]
    exact (Fin.cast_val_eq_self _).symm.trans (congrArg (fun z : ℕ => (z : Word w)) stored.1.2.1.startup.length)
  have midLen := (coreFrame _ (.inl (by omega : levelStart L 0+29 < start))).trans len
  obtain ⟨captured,below,oldGraph⟩ := capture B base positions blocks t f hf X c sel
    live size room oldRep len newBank built copied installed
  have hframe : InputFrame L cur before m := by
    rw [headerMemory,← oldAt]
    exact InputFrame.substep sub adj
  have passFrame := hframe.trans (show InputFrame L cur m out from ⟨fun x _ hi => below x hi,oldGraph⟩)
  have kept (j : ℕ) (lower : 6 ≤ j) (upper : j ≤ 27) : mid (head+j) = before (head+j) := by
    apply (coreFrame _ (.inl (by omega))).trans
    rw [headerMemory]
    apply sub.outside
    · right; rw [oldAt]; omega
    · left; rw [newAt]; omega
    · left; rw [newAt]; change head+j < nextHead+54; omega
  obtain ⟨emission,_⟩ := installed.emits
  have emitted : Emission L cur lev before out :=
    emission.prepend (kept 14 (by decide) (by decide)) (kept 27 (by decide) (by decide))
  have currentGraph (x : ℕ) (hx : CurrentGraph.graphCell L new x ∨ CurrentGraph.startupCell L x ∨
      CurrentGraph.frameCell L x) : out x = finalMemory lev L old new before x := by
    rw [← headerMemory]
    rcases hx with graph | ⟨j,hj,rfl⟩ | frame
    · rw [newAt] at graph
      rcases graph with cell | cell
      · change nextHead ≤ x ∧ x < nextHead+6 at cell
        exact (installed.frame x ⟨.inr (by omega),.inr (by omega),by omega,by omega⟩ (.inr (by omega))).trans
          (coreFrame x (.inr ⟨cell.1,by omega⟩))
      · change nextHead+54 ≤ x ∧ x < incidenceStart L nxt at cell
        exact (installed.frame x ⟨.inr (by omega),.inr (by omega),by omega,by omega⟩ (.inr (by omega))).trans
          (coreFrame x (.inr ⟨by omega,cell.2⟩))
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      exact below _ (by omega)
    · change levelStart L 0+6 ≤ x ∧ x < levelStart L 0+14 at frame
      exact below x (by omega)
  have counts : IncidenceDirectory.slotCount (Y) = (Y).positions*2^(S.degreeExponent 0) := by
    rw [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv g),Fintype.card_fin]
  have successor := CurrentResident.append_substep (v := lev) old new (index.trans oldAt.symm) adj
    stored.1 (by change 30 ≤ 54; decide) room sub (index ▸ emitted) (by
      change (packedIncidence L w new (IncidenceDirectory.slotCount (Y))).Represents (Y) out
      rw [newAt,counts]
      exact captured.new) currentGraph (by simpa only [index] using passFrame.earlier)
  apply DetailedResident.append stored successor
  · rw [index]
    change CompiledResident.RefreshPayload B base positions blocks n cur X c out
    exact ⟨space.live,size,room,captured,installed.child n midLen⟩
  · simpa only [index] using passFrame.earlier
  · simpa only [index] using passFrame.graph

end CompressorRecords.RefreshPayloadHistory

end VPVNP
end Computability
end OAI
