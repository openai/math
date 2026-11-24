import OAI.Computability.VPVNP.CompressorCurrentGraph
import OAI.Computability.VPVNP.CompressorRefreshPlacementPacket
import OAI.Computability.VPVNP.CompressorScheduledGreedyRates
import OAI.Computability.VPVNP.CompressorWindowPackets

/-!
# The three live refresh header publications

The current graph's terminal header becomes the input header of the refresh.
The following two native reports publish the successor dimensions and the
successor's canonical incidence and scratch pointers.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
set_option quotPrecheck false

namespace CompressorRecords.RefreshHeaders

open BurstRAM Compression BlockPlanner DescriptorSpace BlockHeaderRun Schedule SourceOnline
open PortRefresh.TraversalHeaders
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
variable (f : B.Entry → R) (hf : B.IsSolution f) {w g : ℕ} (base : Word w) (positions blocks t : ℕ)
variable (X : State S.portExponent (S.portExponent + g))
variable (c : Compression.Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool)

local notation "v" => RefreshPlacement.selectedLevel B f hf X c sel
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "pub" => Schedule.Ports.data pt
local notation "fl" => Script.levelsPerBlock scr * t
local notation "st" => (levelStart L fl : Word w)
local notation "oldIdx" => fl + S.steps
local notation "newIdx" => fl + (S.steps + 1)
local notation "role" => Scalars.Pass.refresh S.portExponent (S.degreeExponent 0) S.expanderExponent
local notation "bound" => ScheduledRates.headerCap (BlockProgram.geometry B) role
local notation "ls" => BlockHeaderPlan.substep (BlockProgram.geometry B) S.steps role
/-- The interval at the beginning of the refresh group that publishes the level headers. -/
def window : Window scr ls := BlockGroups.refresh B 0
local notation "win" => window B
local notation "fitSix" => (by change 6 ≤ 54; decide)

set_option maxHeartbeats 700000 in
-- The three publisher port banks use the scalar types of the selected refresh.
private theorem header_walk (old new : Fin (L).levels) (hOld : oldIdx = old.val)
    (hNew : newIdx = new.val)
    (m : Memory w) (run : Substep v L old new fitSix m) (fit : endAddress L < 2 ^ w)
    (entry : LevelFields.Entry L fl pub st m) (head : BlockHeaderPlan.firstHeader.eval pub st m =
      header w L 0)
    (pitch : (pub 1 - 1).val < levelStart L old) (count : (pub 3).val < levelStart L old) :
    SourceWalk (Window.Raw (A := scr) L base t bound) ls m (reports v L old new m) ∧
      branchPaths (reports v L old new m) = [[],[],[]] := by
  let mid := inputMemory v L old m
  let next := outputMemory v L old new m
  let r₀ := scalarReport (inputRow v) (header w L old) (header w L old) m
  let r₁ := scalarReport (outputRow v) (header w L old) (header w L new) mid
  let r₂ := headReport L new next
  let q := ls
  have qlen : q.length = 3 := rfl
  have hq₀ : 0 < q.length := by omega
  have hq₁ : 1 < q.length := by omega
  have hq₂ : 2 < q.length := by omega
  obtain ⟨h₀,h₁,h₂⟩ := HeaderPacket.substep v run fit fl S.steps hOld hNew pub st entry head pitch
    count
  have support (mem : Memory w) (j : Fin q.length) :
      HeaderOperands.Supported (Window.operandRegion scr L base) pub st mem q[j.val] :=
    HeaderOperands.substep _ _ _ _ _ _ _ (.inl rfl) (.inr (.inl rfl)) _ (List.getElem_mem ..)
  have c₀ : (inputRow v).recipe.code.length + 1 ≤ bound := le_max_left ..
  have c₁ : (outputRow v).recipe.code.length + 1 ≤ bound := (le_max_left ..).trans (le_max_right ..)
  have c₂ : (DescriptorHeads.publisher (L).shape).recipe.code.length + 1 ≤ bound :=
    (le_max_right ..).trans (le_max_right ..)
  constructor
  · change SourceWalk _ [q[0]'hq₀,q[1]'hq₁,q[2]'hq₂] m ([r₀] ++ ([r₁]++[r₂]))
    refine SourceWalk.next (rs := [r₀]) ⟨_,_,c₀,h₀,support m ⟨0,hq₀⟩⟩ ?_
    simp only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    refine SourceWalk.next (rs := [r₁]) ⟨_,_,c₁,h₁,support mid ⟨1,hq₁⟩⟩ ?_
    simp only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    exact SourceWalk.singleton ⟨_,_,c₂,h₂,support next ⟨2,hq₂⟩⟩
  · have a := ((runSegment_iff ..).mp h₀.execute).2.2
    have b := ((runSegment_iff ..).mp h₁.execute).2.2
    have d := ((runSegment_iff ..).mp h₂.execute).2.2
    exact congrArg₂ (· ++ ·) a (congrArg₂ (· ++ ·) b d)

set_option maxHeartbeats 800000 in
-- Publishing the header in the global script identifies both packed incidence directories.
/-- Native group zero of the installed refresh, including the post-memory
used by the input graph, the incidence copies and the DFS placement rows. -/
theorem install (m : Memory w) (n cap : ℕ) (ht : t < blocks) (size : X.positions ≤ positions)
    (fit : endAddress L < 2 ^ w) (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory - 1).val = (levelWords L : Word w)) (clock : scanCap scr bound ≤ cap)
    (current : CurrentGraph.Current L oldIdx X n m) (sites : X.positions < 2 ^ w)
      (degree : slotDegree S < 2 ^ w) :
    ∃ (old new : Fin (L).levels) (ps : List (Packet scr w)),
      old.val = oldIdx ∧ new.val = newIdx ∧
      SourceOnline.Group scr L base cap ((scr).initial.length + t * (scr).block.length +
        (win).before.length)
        (directoryRows L) m ps ∧ ps.map (fun p ↦ p.stage.phase) = (win).indices ∧
      ps.flatMap SourceWalk.Packet.reports = reports v L old new m ∧
      branchPaths (reports v L old new m) = [[],[],[]] ∧
      Substep v L old new fitSix m ∧
      (packedIncidence L w old (v).oldSlots).Represents X (post m ps) ∧
      HeadBank L old (v).oldSlots (post m ps) ∧ HeadBank L new (v).outputSlots (post m ps) := by
  have hNext : newIdx < (L).levels := by
    have h := Nat.mul_le_mul_left (S.steps + 1) ht
    rw [Nat.mul_succ] at h
    change (S.steps + 1) * t + (S.steps + 1) < 1 + (S.steps + 1) * blocks
    omega
  let old : Fin (L).levels := ⟨oldIdx,by omega⟩
  let new : Fin (L).levels := ⟨newIdx,hNext⟩
  have slot : IncidenceDirectory.slotCount X = (v).oldSlots := by
    change Fintype.card X.Base * 2 ^ (S.portExponent + g) * 2 ^ S.portExponent = X.positions * 2 ^
      S.portExponent
    rw [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv
      (S.portExponent + g)),Fintype.card_fin]
  have capacity : IncidenceDirectory.slotCount X ≤ slotCapacity L := slot ▸ Nat.mul_le_mul size
    (le_max_left ..)
  have adj : old.val + 1 = new.val := by
    change fl + S.steps + 1 = fl + (S.steps + 1)
    omega
  obtain ⟨run,rep,oldBank,newBank⟩ := current.publish v old new adj fitSix fit capacity sites degree
  have Hfit := (levelStart_mono L (Nat.zero_le _)).trans_lt fit
  have low := Window.lowCells (A := scr) L base rfl rfl Hfit
  have hold := levelStart_mono L (Nat.zero_le old.val)
  have entry : LevelFields.Entry L fl pub st m := ⟨rfl,pitch⟩
  have head := BlockHeaderPlan.firstHeader_eval L base m st (Fin.ofNat_val_eq_self base).symm rows
  obtain ⟨raw,quiet⟩ := header_walk B f hf base positions blocks t X c sel old new rfl rfl m run
    fit entry head
    (low.2.trans_le hold) (low.1.trans_le hold)
  have clocks (j : Fin (scr).size) := scanCap_clocks
    (p := ⟨HeaderPacket.attach scr j pub st m bound [],m,[]⟩) _ le_rfl clock
  have live (j : Fin (ls).length) : Window.ordinal (A := scr) t ((win).index j) < directoryRows
    L := by
    rw [(win).ordinal_index,BlockProgram.directory_rows,(scr).calendar_total]
    have pos := ((win).position j).isLt
    have mul := Nat.mul_le_mul_right (scr).block.length ht
    rw [Nat.succ_mul] at mul
    omega
  obtain ⟨ps,grp,phases,logs⟩ := (win).group L base t rfl rfl Hfit cap bound m
    (reports v L old new m) raw
    rows pitch live (fun j _ ↦ (clocks j).1) (fun j _ ↦ (clocks j).2)
  have same : post m ps = finalMemory v L old new m := by rw [post,logs,reports_after]
  refine ⟨old,new,ps,rfl,rfl,grp,phases,logs,quiet,run,?_,?_,?_⟩
  all_goals rw [same]
  · simpa only [← slot] using rep
  · simpa only [← slot] using oldBank
  · exact newBank

end CompressorRecords.RefreshHeaders

end

end VPVNP
end Computability
end OAI
