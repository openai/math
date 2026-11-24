import OAI.Computability.VPVNP.CompressorRefreshHeaderGroup
import OAI.Computability.VPVNP.CompressorRefreshPrepareGroup
import OAI.Computability.VPVNP.CompressorPublishedHeadWindows
import OAI.Computability.VPVNP.CompressorDefaultSelection
import OAI.Computability.VPVNP.CompressorDeterministicGroup

/-!
# From a current graph boundary to the native refresh selector

The three header publishers and the full demand preparation are one quiet
interval. The header reports are independent of the mathematical term.
At its final memory the physical selector sees the original block demands.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
set_option quotPrecheck false

namespace CompressorRecords.RefreshBefore

open BurstRAM BlockPlanner Schedule DescriptorSpace Compression
open BlockHeaderRun SourceOnline SourceTransport PairSimulation.LocalHistory
open PortRefresh PortRefresh.LevelRecipe
open scoped Fin.CommRing
open private publisherCounts from OAI.Computability.VPVNP.CompressorScheduledGreedyRates

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)
variable {w g : ℕ} (base : Word w) (positions blocks t : ℕ) (X : State S.portExponent
    (S.portExponent + g))
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "fl" => Script.levelsPerBlock scr * t
local notation "cur" => fl + S.steps
local notation "nxt" => fl + (S.steps + 1)
local notation "start" => arrayBase L cur
local notation "T" => packedIncidence L w cur (X.positions * 2 ^ S.portExponent)
local notation "role" => Scalars.Pass.refresh S.portExponent (S.degreeExponent 0) S.expanderExponent
local notation "origin" => PassOrigin.refresh (B := B) (f := f) (hf := hf) X
local notation "c₀" => defaultSelection origin
local notation "v" => RefreshPlacement.selectedLevel B f hf X c₀ []
local notation "hwin" => RefreshHeaders.window B
local notation "pwin" => RefreshPrepare.window B
local notation "offset" => (scr).initial.length + t * (scr).block.length + (hwin).before.length
local notation "log" => (fun xs : List (Packet scr w) ↦ xs.flatMap SourceWalk.Packet.reports)
local notation "P" => PortRefresh.Allocation.plan X (S.degreeExponent 0)
  (RefreshBlockPlan.shape B).dH
  (RefreshBlockPlan.shape B).ties (RefreshBlockPlan.shape B).stride start

private theorem reports_charge (V : SelectedLevel B f hf) (K : Layout) (m : Memory w) (a b : ℕ) :
    RAMBuckets.cost Report.probes (reports V K a b m) = ScheduledRates.headerRate K.shape
      (Scalars.ofOrigin V.origin) := by
  have x := publisherCounts (inputRow V) (scalarPorts (header w K a)) (header w K a) m
  have y := publisherCounts (outputRow V) (scalarPorts (header w K b)) (header w K a)
    (inputMemory V K a m)
  have z := publisherCounts (DescriptorHeads.publisher K.shape)
    (headPorts (header w K b) (header w K 0)) 0 (outputMemory V K a b m)
  change (1 + _) + ((1 + _) + ((1 + _) + 0)) = _
  simp only [scalarReport,headReport]
  rw [x.2.1,y.2.1,z.2.1]
  exact (by simp only [ScheduledRates.headerRate,inputRow,outputRow,Nat.add_assoc,Nat.add_zero])

theorem header_charge (m : Memory w) (a b : ℕ) :
    RAMBuckets.cost Report.probes (reports v L a b m) = ScheduledRates.headerRate
      (BlockProgram.geometry B) role :=
  reports_charge B f hf v L m a b

theorem header_choice_independent (c : Compression.Refresh.DyadicRefreshChoice X S.graph
    (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool) (m : Memory w)
      (a b : ℕ) :
    reports (RefreshPlacement.selectedLevel B f hf X c sel) L a b m = reports v L a b m := rfl

/-- Certifies the consecutive header and preparation packet groups before the refresh core,
including their reports, preserved incidence and traversal headers, quiet choices and exact
probe charge. -/
structure Before (cap : ℕ) (m : Memory w) (hs ds : List (Packet scr w)) : Prop where
  group : SourceOnline.Group scr L base cap offset (directoryRows L) m (hs ++ ds)
  phases : (hs ++ ds).map (fun q ↦ q.stage.phase) = (hwin).indices ++ (pwin).indices
  headerReports : log hs = reports v L cur nxt m
  oldLive : cur < (L).levels
  newLive : nxt < (L).levels
  headerRun : Substep v L ⟨cur,oldLive⟩ ⟨nxt,newLive⟩ (by change 6 ≤ 54; decide) m
  counts : LevelFields.Published L cur v (Scalars.ofOrigin (v).origin).expanderDegree (post m hs)
  inputHeader : RefreshCore.Header (Fintype.card X.Base) g (levelStart L cur) start T (post m hs)
  represented : (T).Represents X (post m hs)
  atOldHeads : TraversalHeaders.HeadBank L cur (v).oldSlots (post m hs)
  atNewHeads : TraversalHeaders.HeadBank L nxt (v).outputSlots (post m hs)
  headerPitch : post m hs ((pt).directory - 1).val = (levelWords L : Word w)
  headerRows : post m hs (pt).rows.val = (directoryRows L : Word w)
  data : RefreshPrepare.Prepared B base positions blocks t X (post m hs) (log ds)
  header : RefreshCore.Header (Fintype.card X.Base) g (levelStart L cur) start T (post m (hs ++ ds))
  oldHeads : TraversalHeaders.HeadBank L cur (v).oldSlots (post m (hs ++ ds))
  newHeads : TraversalHeaders.HeadBank L nxt (v).outputSlots (post m (hs ++ ds))
  pitch : post m (hs ++ ds) ((pt).directory - 1).val = (levelWords L : Word w)
  rows : post m (hs ++ ds) (pt).rows.val = (directoryRows L : Word w)
  quiet : ∀ p ∈ hs ++ ds, p.stage.choices = List.replicate p.stage.choices.length []
  charge : RAMBuckets.cost Report.probes (log (hs ++ ds)) =
    ScheduledRates.headerRate (BlockProgram.geometry B) role + (6 * (P).sites + 12 *
      (P).segments + 3 * (P).blocks * (RefreshBlockPlan.shape B).ties)

private theorem next_window :
    (hwin).before.length + 3 = (pwin).before.length := by
  change (BlockGroups.refresh B 0).before.length + 3 = (BlockGroups.refresh B 1).before.length
  rw [BlockGroups.refresh_offset,BlockGroups.refresh_offset]
  rfl

set_option maxHeartbeats 900000 in
-- The two packet groups share dependent representations of the old and successor headers.
theorem run (termCap cap : ℕ) (m : Memory w) (n : ℕ) (ht : t < blocks) (size : X.positions ≤
    positions)
    (fit : endAddress L < 2 ^ w) (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory - 1).val = (levelWords L : Word w))
    (headerClock : scanCap scr (ScheduledRates.headerCap (BlockProgram.geometry B) role) ≤ cap)
    (termClock : scanCap scr (max 64 termCap) ≤ cap) (current : CurrentGraph.Current L cur X n m)
    (sites : X.positions < 2 ^ w) (degree : slotDegree S < 2 ^ w)
    (width : 2 ^ S.portExponent * X.maxWireWidth < 2 ^ w) (pos : 0 < termCap) :
    ∃ hs ds, Before B f hf base positions blocks t X cap m hs ds := by
  obtain ⟨oi,ni,hs,old,new,hgroup,hlabels,hl,quiet,hsub,rep,oldBank,newBank⟩ :=
    RefreshHeaders.install B f hf base positions blocks t X c₀ [] m n cap ht size fit rows pitch
      headerClock
      current sites degree
  let mid := post m hs
  have hm : mid = finalMemory v L oi ni m := by
    change after m (eventLog (hs.flatMap SourceWalk.Packet.reports)) = _
    rw [hl,reports_after]
  have Hfit := (levelStart_mono L (Nat.zero_le _)).trans_lt fit
  have low := Window.lowCells (A := scr) L base rfl rfl Hfit
  have oLe := levelStart_mono L (Nat.zero_le oi.val)
  have nLe := levelStart_mono L (Nat.zero_le ni.val)
  have lowEq (a : ℕ) (ha : a < levelStart L 0) : mid a = m a := by
    rw [hm]
    exact hsub.outside a (.inl (ha.trans_le oLe)) (.inl (ha.trans_le nLe)) (.inl (by omega))
  have mr := (lowEq _ low.1).trans rows
  have mp := (lowEq _ low.2).trans pitch
  have curr : LevelFields.Published L cur v (Scalars.ofOrigin (v).origin).expanderDegree mid := by
    rw [← old,hm]; exact hsub.input
  rw [old] at rep oldBank
  rw [new] at newBank
  have hr := PublishedHeads.level_room B base positions blocks t S.steps ht le_rfl fit
  have head : RefreshCore.Header (Fintype.card X.Base) g (levelStart L cur) start T mid :=
    RefreshCore.Header.ofPublished curr oldBank rfl (by change 0 < 6; decide) (by omega)
  obtain ⟨ds,dgroup,dlabels,prep⟩ := RefreshPrepare.install B base positions blocks t X termCap
    cap mid
    ht size fit mr mp termClock head rep width pos
  have hlen : hs.length = 3 := by
    have card : (hwin).indices.length = 3 := by
      rw [Window.indices,List.length_ofFn]
      exact BlockHeaderPlan.substep_length ..
    exact (List.length_map _).symm.trans ((congrArg List.length hlabels).trans card)
  have offsetEq : offset + hs.length = (scr).initial.length + t * (scr).block.length +
    (pwin).before.length := by
    rw [hlen,Nat.add_assoc,next_window]
  have both := hgroup.append (offsetEq.symm ▸ dgroup)
  have dataMem : post m (hs ++ ds) = after mid (eventLog (log ds)) := post_append ..
  have span : levelStart L cur + 66 ≤ start := by
    change _ ≤ levelStart L cur + 66 + 6 * slotCapacity L; omega
  have endOf := (BlockLevelFit.refresh B base.val positions blocks oi rfl X size fit).1.next
  rw [old] at endOf
  change (PortRefresh.Allocation.plan X (S.degreeExponent 0) (RefreshBlockPlan.shape B).dH
    (RefreshBlockPlan.shape B).ties (RefreshBlockPlan.shape B).stride (start + 0 * tableWords
      L)).stop ≤
    levelStart L (cur + 1) at endOf
  simp only [Nat.zero_mul,Nat.add_zero,show cur + 1 = nxt by omega] at endOf
  have keep (a : ℕ) (away : a < start ∨ levelStart L nxt ≤ a) : post m (hs ++ ds) a = mid a := by
    rw [dataMem]
    exact after_outside mid prep.writes (by
      intro hit
      change start ≤ a ∧ a < (P).stop at hit
      omega)
  have lower := levelStart_mono L (Nat.zero_le (cur))
  have hhead := head.keep (fun i hi ↦ keep _ (.inl (by omega)))
  have ho := oldBank.keep (m' := post m (hs ++ ds)) (fun i hi ↦ keep _ (.inl
    (by change i < 66 at hi; omega)))
  have hn := newBank.keep (m' := post m (hs ++ ds)) (fun i _ ↦ keep _ (.inr (Nat.le_add_right ..)))
  have paths : (hs ++ ds).flatMap (fun p ↦ p.stage.choices) = List.replicate (3 +
    (log ds).length) [] := by
    rw [PublishedHeads.chronological_tapes m _ both.chronological,List.flatMap_append,hl,
      branchPaths,
      List.map_append,← branchPaths,← branchPaths,quiet,prep.quiet,List.replicate_add]
    rfl
  have ol : cur < (L).levels := old ▸ oi.isLt
  have nl : nxt < (L).levels := new ▸ ni.isLt
  have so : oi = (⟨cur,ol⟩ : Fin (L).levels) := Fin.ext old
  have sn : ni = (⟨nxt,nl⟩ : Fin (L).levels) := Fin.ext new
  refine ⟨hs,ds,both,by rw [List.map_append,hlabels,dlabels],old ▸ new ▸ hl,ol,nl,so ▸ sn ▸ hsub,
    curr,head,rep,oldBank,newBank,mp,mr,prep,hhead,ho,hn,
    (keep _ (.inl (by omega))).trans mp,(keep _ (.inl (by omega))).trans mr,
    ScheduledTrace.packet_quiet_of_flat paths,?_⟩
  change RAMBuckets.cost Report.probes ((hs ++ ds).flatMap SourceWalk.Packet.reports) = _
  rw [List.flatMap_append,hl,RAMBuckets.cost_append,header_charge,prep.charge]

end CompressorRecords.RefreshBefore

end

end VPVNP
end Computability
end OAI
