import OAI.Computability.VPVNP.CompressorShrinkHeaderGreedyPackets
import OAI.Computability.VPVNP.CompressorShrinkHeaderGreedyTapes
import OAI.Computability.VPVNP.CompressorShrinkBundlePrepared
import OAI.Computability.VPVNP.CompressorShrinkTermGroup
import OAI.Computability.VPVNP.CompressorRecordsShrinkBranch

/-! # The actual shrinking calendar up to the selected term rows

The same memory that receives the three header publications feeds the greedy,
placement, bundle, and absolute-ID workers. The gather and the term selection
then use the demand widths computed by those workers. The complete prefix
has twenty-two visits at their concrete global ordinals.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledPrefix

open BurstRAM BlockPlanner DescriptorSpace Compression BlockHeaderRun SourceOnline
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)
variable {g w : ℕ} (X : GreedyArena.ShrinkingState (ShrinkBlockInputs.a i) g)
variable (sel : SelectedScore.Selection B X) (tape : List Bool) (base : Word w)
variable (positions blocks t : ℕ)
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B (Fin.val base) positions blocks
local notation "pt" => Workspace.ports (Schedule.arity (Script.catalog (BlockProgram.script B))) base
local notation "H" => levelStart L 0
local notation "first" => (S.steps+1)*t
local notation "v" => PairSimulation.TraversalRows.shrinkLevel B f hf i X sel tape
local notation "atStart" => List.length (Script.initial scr)+t*List.length (Script.block scr)+List.length (BlockIndex.earlier B i)

variable (old new : Fin (BlockProgram.layout B (Fin.val base) positions blocks).levels) (m : Memory w) (T : IncidenceDirectory w)
local notation "start" => tableBase L old (0 : Fin 6)
local notation "headPost" => finalMemory v L old new m
local notation "hdr" => ShrinkGreedyHeaderValues.Header i X T L first start (Schedule.Ports.data pt) (levelStart L first : Word w)
local notation "Pkt" => SourceOnline.Packet scr w

set_option maxHeartbeats 1200000 in
/-- The physical reports and memory before the first gather, together with the
published fields the term planner will read in that memory. -/
theorem before_gather (oldAt : first+i.val=old.val) (next : old.val+1=new.val)
    (sub : Substep v L old new (by change 6 ≤ 54; decide) m) (fuel : ℕ)
    (p : ShrinkBranch.Prefix X T start fuel headPost)
    (heads : ∀ c : Fin 6, m (incidenceHead L old c)=T.column c)
    (scratch : m (tableHead L old (0 : Fin 6))=(start : Word w))
    (low : ∀ c, H ≤ (T.column c).val)
    (fit : endAddress L < 2^w) (room : ShrinkInput.stop X start < 2^w)
    (rows : m (pt).rows.val=(directoryRows L : Word w))
    (pitch : m ((pt).directory-1).val=(levelWords L : Word w))
    (within : t < blocks) (cap : ℕ) (headClock : ShrinkHeaderGreedyPackets.clock B i ≤ cap)
    (denseClock : scanCap scr (ShrinkBundlePackets.maxFuel B i) ≤ cap) :
    ∃ ps : List Pkt, Group scr L base cap atStart (directoryRows L) m ps ∧ ps.length=20 ∧
      ps.flatMap SourceWalk.Packet.reports =
        (BlockHeaderRun.reports v L old new m ++ p.input.reports) ++ p.absolute ∧
      post m ps = after p.input.post (eventLog p.absolute) ∧
      hdr headPost ∧ hdr (after p.input.post (eventLog p.absolute)) ∧
      (∀ q ∈ ps, ∀ bs ∈ q.stage.choices, bs = []) := by
  let absMem := after p.input.post (eventLog p.absolute)
  have hH : H < 2^w := (levelStart_mono L (Nat.zero_le (L).levels)).trans_lt fit
  have cells := Window.lowCells (A:=scr) L base (BlockProgram.layout_arity B ..).symm rfl hH
  have here := levelStart_mono L (Nat.zero_le old.val)
  have entry : LevelFields.Entry L first (pt).data (levelStart L first : Word w) m := ⟨rfl,pitch⟩
  have header : hdr headPost := ShrinkGreedyHeaderValues.post_header B i X f hf sel tape base positions blocks
    T first old new oldAt.symm next.symm m sub fit _ _ entry (cells.2.trans_le here) heads scratch
  have postRows := (sub.before v next (pt).rows.val (cells.1.trans_le here)).trans rows
  obtain ⟨hs,hg,phases,hlogs,hpost⟩ := ShrinkHeaderGreedyPackets.group B f hf i X sel tape base
    positions blocks t old new oldAt next m sub T p.input.greedy heads scratch low fit rows pitch within cap headClock
  obtain ⟨ds,dg,labels,dlogs,dpost⟩ := ShrinkBundlePackets.group B i X T start base positions blocks t
    p.input p.absolute p.absoluteRun room low within header postRows cap denseClock
  have hlen : hs.length=9 := by
    calc
      hs.length = (ShrinkHeaderGreedyPackets.window B i).indices.length := by
        simpa only [List.length_map] using congrArg List.length phases
      _ = (ShrinkHeaderGreedyPackets.visits B i).length := List.length_ofFn
      _ = 9 := ShrinkHeaderGreedyPackets.visits_length B i
  have dlen : ds.length=11 := by
    calc
      ds.length = ShrinkBundlePackets.stages.length := by
        simpa only [List.length_map,List.length_ofFn] using congrArg List.length labels
      _ = 11 := by decide
  rw [ShrinkBundlePackets.startOrdinal_eq] at dg
  have together := hg.append (by rw [hpost,hlen]; exact dg)
  have floor : start ≤ (ShrinkInput.plan X start).gathered := by
    have pre := (ShrinkInput.range_bounds X start).1.trans (ShrinkInput.range_bounds X start).2.1
    apply pre.trans
    change ShrinkInput.rankBase X start ≤ ((ShrinkInput.rankBase X start + 2*(ShrinkInput.plan X start).A) +
      2*(ShrinkInput.plan X start).B) + (ShrinkInput.plan X start).rectangleSize
    omega
  have keep (x : ℕ) (hx : x < start) : absMem x = headPost x :=
    (p.absoluteRun.frame x (.inl (hx.trans_le floor))).trans (p.input.below x hx)
  have hempty := ShrinkHeaderGreedyPackets.empty_choices v sub p.input.greedy hg.chronological hlogs
  have dempty (q : Pkt) (hq : q ∈ ds) (bits : List Bool) (hb : bits ∈ q.stage.choices) : bits = [] := by
    have mem : q.stage ∈ ds.map SourceWalk.Packet.stage := List.mem_map_of_mem hq
    rw [labels,List.mem_ofFn] at mem
    obtain ⟨j,hj⟩ := mem
    rw [← hj] at hb
    exact (List.mem_replicate.mp hb).2
  refine ⟨hs++ds,together,by rw [List.length_append,hlen,dlen],?_,?_,header,header.keep_below keep,?_⟩
  · rw [List.flatMap_append,hlogs,dlogs]
    simp only [ShrinkInput.Run.reports,ShrinkBundlePlan.Scheduled.preparationReports,List.append_assoc]
  · rw [post_append,hpost,dpost]
  · intro q hq bs hb
    exact (List.mem_append.mp hq).elim (fun h => hempty q h bs hb) (fun h => dempty q h bs hb)

set_option maxHeartbeats 1200000 in
/-- The first twenty-one visits are deterministic. The final packet runs the
true term worker on the memory built by the preceding gather, and its tapes
are the ordered words of the prescribed shrinking selection. -/
theorem through_selection (oldAt : first+i.val=old.val) (next : old.val+1=new.val)
    (sub : Substep v L old new (by change 6 ≤ 54; decide) m) (fuel : ℕ)
    (p : ShrinkBranch.Prefix X T start fuel headPost)
    (chosen : ShrinkBranch.Selected B X T start (10 : Word w) (B.shrink.selectorBits : Word w)
      fuel headPost p sel)
    (heads : ∀ c : Fin 6, m (incidenceHead L old c)=T.column c)
    (scratch : m (tableHead L old (0 : Fin 6))=(start : Word w)) (low : ∀ c, H ≤ (T.column c).val)
    (fit : endAddress L < 2^w) (room : ShrinkInput.termEnd X start 10 < 2^w)
    (rows : m (pt).rows.val=(directoryRows L : Word w)) (pitch : m ((pt).directory-1).val=(levelWords L : Word w))
    (within : t < blocks) (cap : ℕ) (headClock : ShrinkHeaderGreedyPackets.clock B i ≤ cap)
    (denseClock : scanCap scr (ShrinkBundlePackets.maxFuel B i) ≤ cap)
    (gatherClock : ShrinkDemandGather.cost < fuel) (termClock : scanCap scr fuel ≤ cap) :
    ∃ pre : List Pkt, ∃ last : Pkt,
      Group scr L base cap atStart (directoryRows L) m pre ∧ pre.length=21 ∧
      (∀ q ∈ pre, ∀ bs ∈ q.stage.choices, bs = []) ∧
      pre.flatMap SourceWalk.Packet.reports = BlockHeaderRun.reports v L old new m ++ p.reports ∧
      post m pre = p.beforeTerm ∧ last.input = p.beforeTerm ∧
      last.stage = ShrinkTermOnline.globalVisit B i X T start sel fuel .select ∧
      last.stage.choices = List.ofFn (ShrinkTermSelection.tapes B.shrink X sel w) ∧ last.reports=chosen.terms ∧
      Group scr L base cap atStart (directoryRows L) m (pre++[last]) ∧
      post m (pre++[last]) = after p.beforeTerm (eventLog chosen.terms) ∧
      hdr p.beforeTerm := by
  have stopFit : ShrinkInput.stop X start < 2^w := by unfold ShrinkInput.termEnd at room; omega
  obtain ⟨ps,gp,nps,reports,post₀,hbefore,habs,empty⟩ := before_gather B f hf i X sel tape base
    positions blocks t old new m T oldAt next sub fuel p heads scratch low fit stopFit rows pitch within cap headClock denseClock
  let absMem := after p.input.post (eventLog p.absolute)
  let ga := ShrinkTermOnline.packet B i X T start sel fuel .gather absMem p.gather
  let te := ShrinkTermOnline.packet B i X T start sel fuel .select p.beforeTerm chosen.terms
  have cert := ShrinkTermOnline.branch_group B i X T start sel fuel base positions blocks t cap headPost p chosen
    gatherClock room hbefore.raw hbefore.fieldsBelow within termClock
  have two : Group scr L base cap (atStart+20) (directoryRows L) absMem [ga,te] := cert.1
  have g := Group.singleton ga rfl two.chronological.2.1 (two.checked ga (by simp))
    (show Prepared scr L base (atStart+20) (directoryRows L) ga by simpa using two.prepared 0)
  have before := gp.append (by rw [post₀,nps]; exact g)
  have all := gp.append (by rw [post₀,nps]; exact two)
  have preg : post m (ps++[ga]) = p.beforeTerm := by
    rw [post_append,post₀]
    simp only [post,List.flatMap_cons,List.flatMap_nil,List.append_nil,ga,ShrinkTermOnline.packet,
      ShrinkBranch.Prefix.beforeTerm,absMem]
  have daddr : (ShrinkInput.demandHead (w:=w) X start).val = ShrinkInput.stop X start :=
    Nat.mod_eq_of_lt stopFit
  have stLe := ShrinkInput.range_bounds X start
  have keep (x : ℕ) (hx : x<start) : p.beforeTerm x = absMem x :=
    p.gatherRun.frame x (.inl (by
      change x < (ShrinkInput.demandHead (w:=w) X start).val
      rw [daddr]; exact hx.trans_le (stLe.1.trans (stLe.2.1.trans (stLe.2.2.1.trans stLe.2.2.2)))))
  refine ⟨ps++[ga],te,before,by simp only [List.length_append,List.length_cons,List.length_nil,nps],?_,?_,
    preg,rfl,rfl,rfl,rfl,?_,?_,habs.keep_below keep⟩
  · intro q hq bs hb
    rcases List.mem_append.mp hq with hq|hq
    · exact empty q hq bs hb
    · rcases List.mem_singleton.mp hq with rfl
      exact (List.mem_replicate.mp hb).2
  · simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,reports,ga,
      ShrinkTermOnline.packet,ShrinkBranch.Prefix.reports,List.append_assoc]
  · simpa only [List.append_assoc,List.singleton_append] using all
  · rw [post_append,preg]
    simp only [post,List.flatMap_cons,List.flatMap_nil,List.append_nil,te,ShrinkTermOnline.packet]

end CompressorRecords.ShrinkScheduledPrefix

end

end VPVNP
end Computability
end OAI
