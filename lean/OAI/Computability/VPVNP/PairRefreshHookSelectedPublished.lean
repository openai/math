import OAI.Computability.VPVNP.PairRefreshHookSelectedLocation
import OAI.Computability.VPVNP.PairRefreshSelectedSite
import OAI.Computability.VPVNP.CompressorRefreshPayloadHistory
import OAI.Computability.VPVNP.CompressorSelectedChildDirectory

/-!
# Physical publication of the selected refresh hook

The completed compressor supplies the chosen term, both packed incidence
directories and the child decoder's fields. The selected DFS arena supplies
the actual singleton row and the level locator. Their combination describes
the native hook at the popped port.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.RefreshHook.SelectedPublished

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh CompressorRecords
open PortRefresh NewSlots LocalHistory TraversalRoles TraversalRows TraversalControllerInputs
open DescriptorSpace NodeArguments NodeArguments.ChildScan
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f) {g n w hist l : ℕ}
  (T : ℕ) (hT : T * S.laneBits ≤ l) (initial : State (S.degreeExponent 0) l)
  (z : (B.execute f hf T hT initial).Choices) (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh) (encoded : List Bool)
  (port : (X.Base × BitWord g) × Fin (2 ^ S.portExponent))
  (stage : Fin (executeLevels B f hf T hT initial z).length)
  (occurrence : (executeLevels B f hf T hT initial z)[stage] =
    RefreshPlacement.traversalLevel f hf X choice encoded)
  (workspace positions blocks : ℕ)

local notation "layout" => BlockProgram.layout B workspace positions blocks
local notation "levels" => executeLevels B f hf T hT initial z
local notation "tags" => TraversalRoles.selected B f hf T hT initial z
local notation "cap" => BlockSchedule.Templates.recordLimit B
local notation "first" => endAddress layout
local notation "rowEnd" => first + tagWords cap tags
local notation "ord" => Fin.val (sites X.baseIndex (bitWordFinEquiv g) port)
local notation "older" => layerBase cap first tags stage.val
local notation "child" => address cap older ord
local notation "parent" => address cap (layerBase cap first tags (stage.val + 1)) ord
local notation "width" =>
  State.totalWidth (StateExecution.finalState (B.execute f hf T hT initial) z)
local notation "leaf" => TaggedLayer.mk (leafLayer (siteOrder initial)) Role.cursor
local notation "shape" => RefreshBlockPlan.shape B
local notation "ties" => RefreshBlockPlan.order B
local notation "stride" => LevelRecipe.Shape.stride shape

include occurrence in
/-- Recover the selected row's complete hook data in the memory in which it will
execute. All packed operands come from the producing refresh's physical records. -/
theorem from_resident
    (fits : TraversalPlan.Room B X choice port (slotDegree S) n rowEnd child parent hist w)
    (size : X.positions ≤ positions) (live : stage.val + 1 < (layout).levels)
    {pub : Fin 11 → BurstRAM.Word w} {mem : Memory w} {H offset : ℕ}
    (ds : (i : Fin (levels).length) → LevelDirectory levels[i] mem first)
    (resident : Resident pub mem H (levelStart layout 0) (levelWords layout) offset cap first leaf
      (levelFibers levels ds))
    (rows : AllRows w mem cap first first (selectedLayers B f hf T hT initial z))
    (records : RefreshPayloadHistory.Data B layout stage.val n X choice mem)
    (directory : SelectedChildDirectory.Stored B layout stage.val n X mem) :
    let R := ofSelected B n hist w workspace positions blocks X choice port stage.val
      tags width fits
    R.Published ties stride pub mem := by
  let R := ofSelected B n hist w workspace positions blocks X choice port stage.val tags width fits
  change R.Published ties stride pub mem
  let fibers := levelFibers levels ds
  have len : fibers.length = (levels).length := by simp [fibers, levelFibers]
  have tagEq : leaf :: fibers.map Prod.fst = tags := by
    change leaf :: (levelFibers levels ds).map Prod.fst = _
    rw [levelFibers_tags]
    rfl
  have start_eq (i : ℕ) : levelStart layout 0 + i * levelWords layout = levelStart layout i := by
    simp only [levelStart, Nat.zero_mul, Nat.add_zero]
  have heads (i : ℕ) : levelHead pub mem i = (levelStart layout i : BurstRAM.Word w) := by
    rw [levelHead, terminal_read resident 16 (by decide), terminal_read resident 17 (by decide),
      resident.firstHead, resident.levelPitch, ← Nat.cast_mul, ← Nat.cast_add, start_eq]
  have headVal (i : ℕ) (hi : i ≤ fibers.length) :
      (levelHead pub mem i).val = levelStart layout i := by
    have room := resident.levelFits i hi
    rw [start_eq] at room
    rw [heads, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have oldLive : stage.val ≤ fibers.length := stage.isLt.le.trans_eq len.symm
  have newLive : stage.val + 1 ≤ fibers.length := stage.isLt.trans_eq len.symm
  have oldBase := resident.currentBase stage.val oldLive
  rw [start_eq, show leaf :: (levelFibers levels ds).map Prod.fst = tags from tagEq] at oldBase
  let regs := TerminalLayout.privateRegions (slotDegree S) n rowEnd hist
  have bound : rowEnd ≤ regs.histBase := by
    change rowEnd ≤ n + rowEnd * (2 * slotDegree S * n + 1)
    exact (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (Nat.le_add_left ..)
  have cache : regs.histBase ≤ regs.cacheBase := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have arenaFit : rowEnd < 2 ^ w := (bound.trans cache).trans_lt fits.capacity.room
  have tagLive : stage.val < (tags).length := by
    simpa only [TraversalRoles.selected, List.length_cons, List.length_map] using
      stage.isLt.trans (Nat.lt_succ_self _)
  obtain ⟨pos, before, role, histAfter, strideFit, lanesFit, wide, _⟩ := numeric B n hist w
    workspace positions blocks X choice port stage.val tags width fits ⟨stage.val, by omega⟩
    ⟨stage.val + 1, live⟩ size tagLive
    (selected_positive B f hf T hT initial z _ (List.getElem_mem (l := tags) tagLive))
  obtain ⟨j, id, loc, hj, hid, later, addr, endFit⟩ :=
    SelectedLocation.locate B f hf T hT initial z X choice encoded port stage occurrence
      ds resident arenaFit
  have childRow := SelectedLocation.child_row B f hf T hT initial z X choice encoded port
    stage occurrence rows
  refine ⟨⟨H, levelStart layout 0, levelWords layout, offset, first, leaf, fibers, j, id,
    loc, hj, hid, later, addr, endFit⟩, ?_, ?_, ?_, records.fits, records.stored,
    records.old.actual, records.new.actual, pos, before, role, histAfter, strideFit, lanesFit, wide⟩
  · change (ChildScan.directory S.portExponent older cap R.arena R.prev).Stored mem
      (levelHead pub mem stage.val + 14)
    rw [heads]
    exact directory.bank older oldBase
  · change DFS.Row mem parent (parent + 2) [word R.oldNode]
    rw [show R.oldNode = child from oldNode_eq B n hist w workspace positions blocks X choice port
      stage.val tags width fits]
    exact childRow
  · change TraversalHeaders.Geometry (Fintype.card X.Base) g (levelHead pub mem stage.val).val
      (levelHead pub mem (stage.val + 1)).val (arrayBase layout stage.val) R.arena R.prev R.next mem
    rw [headVal _ oldLive, headVal _ newLive]
    exact records.geometry

end PairSimulation.RefreshHook.SelectedPublished

end

end VPVNP
end Computability
end OAI
