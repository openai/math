import OAI.Computability.VPVNP.CompressorShrinkScheduledPrefix
import OAI.Computability.VPVNP.CompressorShrinkSelectedGroup
import OAI.Computability.VPVNP.CompressorShrinkGeometryHeadRetention
import OAI.Computability.VPVNP.CompressorSourceGroupSplit
import OAI.Computability.VPVNP.CompressorBlockShrinkPrefixFits

/-!
# The shrinking calendar through the selected geometry

The first twenty-one visits prepare the physical selector input. One visit
runs the prescribed selection. The following fourteen visits score its
terms and build the selected placement, role, and child directories.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledGeometry

open BurstRAM BlockPlanner DescriptorSpace Compression BlockHeaderRun SourceOnline SourceTransport
open ShrinkSlots SlotLevel
open scoped Fin.CommRing

variable {w : ℕ}

private theorem below_data {A : Script} {L : Layout} {base : Word w} {cap ord total : ℕ}
    {m : Memory w} {ps : List (Packet A w)} (run : Group A L base cap ord total m ps)
    {x : ℕ} (hx : x < levelStart L 0) : post m ps x = m x := by
  apply after_outside m (data := (levelStart L 0 ≤ ·)) _ (Nat.not_le_of_gt hx)
  intro a value ha
  change Event.write a value ∈ (ps.flatMap SourceWalk.Packet.reports).flatMap Report.events at ha
  obtain ⟨r,hr,ev⟩ := List.mem_flatMap.mp ha
  obtain ⟨q,hq,hr⟩ := List.mem_flatMap.mp hr
  exact (run.checked q hq).write a value (List.mem_flatMap.mpr ⟨r,hr,ev⟩)

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)
variable {g w : ℕ} (X : GreedyArena.ShrinkingState (ShrinkBlockInputs.a i) g)
variable (sel : SelectedScore.Selection B X) (tape : List Bool) (base : Word w) (positions blocks t : ℕ)
local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (Schedule.arity (Script.catalog (BlockProgram.script B))) base
local notation "first" => (S.steps+1)*t
local notation "level" => PairSimulation.TraversalRows.shrinkLevel B f hf i X sel tape
local notation "offset" => List.length (Script.initial prog)+t*List.length (Script.block prog)+List.length (BlockIndex.earlier B i)
local notation "total" => directoryRows L
local notation "H" => levelStart L 0
local notation "Pkt" => SourceOnline.Packet prog w
variable (old new : Fin (BlockProgram.layout B base.val positions blocks).levels) (m : Memory w)
local notation "start" => tableBase L old (0 : Fin 6)
local notation "T" => packedIncidence L w old (DemandRAM.oldCount X)
local notation "initial" => finalMemory level L old new m
local notation "headers" => BlockHeaderRun.reports level L old new m
local notation "s" => levelShape (b := ShrinkBlockInputs.b i) X
local notation "rawHeader" => ShrinkHeaderReads.Header i X T start L first
local notation "headBank" => PortRefresh.TraversalHeaders.HeadBank L

set_option maxHeartbeats 1800000

/-- A scheduled execution of shrink geometry in 36 packets. The 21 prefix packets, selector and
14 suffix packets reproduce the branch events and leave the required headers and head banks
in memory before output. -/
structure Result (fuel : ℕ) (p : ShrinkBranch.Prefix X T start fuel initial)
    (v : ShrinkBranch.Selected B X T start (10 : Word w) (B.shrink.selectorBits : Word w) fuel initial p sel) (cap : ℕ) (pre : List Pkt) (selector : Pkt) (tail : List Pkt) : Prop where
  prefixGroup : Group prog L base cap offset total m pre
  prefixLength : pre.length = 21
  prefixEmpty : ∀ q ∈ pre, ∀ bs ∈ q.stage.choices, bs = []
  prefixReports : pre.flatMap SourceWalk.Packet.reports = headers++p.reports
  prefixPost : post m pre = p.beforeTerm
  selected : Group prog L base cap (offset+21) total p.beforeTerm [selector]
  selectInput : selector.input = p.beforeTerm
  selectStage : selector.stage = ShrinkTermOnline.globalVisit B i X T start sel fuel .select
  selectChoices : selector.stage.choices = List.ofFn (ShrinkTermSelection.tapes B.shrink X sel w)
  selectReports : selector.reports = v.terms
  selectOutput : selector.output = after p.beforeTerm (eventLog v.terms)
  suffix : Group prog L base cap (offset+22) total selector.output tail
  suffixLength : tail.length = 14
  suffixEmpty : ∀ q ∈ tail, ∀ bs ∈ q.stage.choices, bs = []
  suffixTapes : tail.flatMap (fun q => q.stage.choices) = List.replicate (SelectedTailPackets.selectedCalls X) []
  suffixEvents : eventLog (tail.flatMap SourceWalk.Packet.reports) = eventLog v.geometry.reports
  whole : Group prog L base cap offset total m (pre++selector::tail)
  length : (pre++selector::tail).length = 36
  events : eventLog ((pre++selector::tail).flatMap SourceWalk.Packet.reports) =
    eventLog ((headers++p.reports)++v.reports)
  final : post m (pre++selector::tail) = v.beforeOutput
  beforeHeader : rawHeader p.beforeTerm
  beforeRows : p.beforeTerm (pt).rows.val = (total : Word w)
  beforePitch : p.beforeTerm ((pt).directory-1).val = (levelWords L : Word w)
  header : rawHeader v.beforeOutput
  rows : v.beforeOutput (pt).rows.val = (total : Word w)
  pitch : v.beforeOutput ((pt).directory-1).val = (levelWords L : Word w)
  oldHeads : headBank old (DemandRAM.oldCount X) v.beforeOutput
  nextHeads : headBank new (actualCount s) v.beforeOutput
  frame : ∀ x, x < start ∨ levelStart L new ≤ x → v.beforeOutput x = initial x

/-- Join the deterministic prefix, prescribed selector and deterministic
geometry at their exact calendar ordinals and machine memories. -/
theorem run (fuel : ℕ) (p : ShrinkBranch.Prefix X T start fuel initial)
    (v : ShrinkBranch.Selected B X T start (10 : Word w) (B.shrink.selectorBits : Word w) fuel initial p sel) (oldAt : first+i.val=old.val) (next : old.val+1=new.val)
    (sub : Substep level L old new (by change 6 ≤ 54; decide) m)
    (fits : ShrinkBranch.PrefixFits B X T start (10 : Word w) fuel)
    (oldHeads : headBank old (DemandRAM.oldCount X) m)
    (low : ∀ c, H ≤ ((T).column c).val) (room : endAddress L < 2^w)
    (sitesFit : X.positions ≤ positions) (within : t < blocks)
    (rows : m (pt).rows.val = (total : Word w)) (pitch : m ((pt).directory-1).val = (levelWords L : Word w))
    (cap : ℕ) (headerClock : ShrinkHeaderGreedyPackets.clock B i ≤ cap)
    (denseClock : scanCap prog (ShrinkBundlePackets.maxFuel B i) ≤ cap)
    (termClock : scanCap prog fuel ≤ cap) (geometryClock : scanCap prog 65 ≤ cap) :
    ∃ pre selector tail, Result B f hf i X sel tape base positions blocks t old new m fuel p v cap pre selector tail := by
  have stride : (10 : Word w).val = 10 := Nat.le_antisymm (Nat.mod_le ..) fits.wide
  have termRoom := fits.termRoom
  rw [stride] at termRoom
  have heads (c : Fin 6) : m (incidenceHead L old c) = (T).column c := by
    rw [packed_column]; exact oldHeads.incidence c
  obtain ⟨pre,selector,gp,npre,empty,plogs,ppost,hin,stage,choices,logs,gs,spost,before⟩ :=
    ShrinkScheduledPrefix.through_selection B f hf i X sel tape base positions blocks t old new m T
      oldAt next sub fuel p v heads (oldHeads.tables (0 : Fin 6)) low room termRoom rows pitch within cap headerClock
      denseClock fits.gatherClock termClock
  have hH := (levelStart_mono L (Nat.zero_le (L).levels)).trans_lt room
  have cells := Window.lowCells (A := prog) L base rfl rfl hH
  have beforeRows : p.beforeTerm (pt).rows.val = (total : Word w) := by
    exact (congrFun ppost _).symm.trans ((below_data gp cells.1).trans rows)
  have beforePitch := before.entry.pitch
  have geomRoom := ShrinkBranch.selected_geometry_fit B i X base.val positions blocks old sitesFit room
  obtain ⟨tail,gt,ntail,tailEvents,tailPost,tailChoices⟩ :=
    SelectedTailPackets.selected_group B i X T start base positions blocks t sel initial fuel cap
      p v fits geomRoom before.raw before.fieldsBelow low beforeRows beforePitch within room geometryClock
  have selectGroup := gs.split.2
  rw [npre,ppost] at selectGroup
  have selectOut : selector.output = after p.beforeTerm (eventLog v.terms) := by
    simp only [SourceWalk.Packet.output,hin,logs]
  have full := gs.append (by
    rw [spost,List.length_append,List.length_singleton,npre]; exact gt)
  have postFull : post m (pre++selector::tail) = v.beforeOutput := by
    have joined := (post_append m (pre++[selector]) tail).trans
      ((congrArg (fun z => post z tail) spost).trans tailPost)
    simpa only [List.append_assoc,List.singleton_append] using joined
  have gfull : Group prog L base cap offset total m (pre++selector::tail) := by
    simpa only [List.append_assoc,List.singleton_append] using full
  have keep (x : ℕ) (hx : x < start) : v.beforeOutput x = p.beforeTerm x := by
    have ranges := ShrinkInput.range_bounds X start
    have oldLimit := hx.trans_le (ranges.1.trans (ranges.2.1.trans (ranges.2.2.1.trans ranges.2.2.2)))
    have stopFit : ShrinkInput.stop X start < 2^w := by unfold ShrinkInput.termEnd at termRoom; omega
    have daddr : (ShrinkInput.demandHead (w := w) X start).val = ShrinkInput.stop X start := Nat.mod_eq_of_lt stopFit
    exact (v.lowerFrame x oldLimit).trans (p.gatherRun.frame x (.inl (by
      change x < (ShrinkInput.demandHead (w := w) X start).val; rwa [daddr]))).symm
  have afterHeader := before.keep_below keep
  have banks := ShrinkGeometryHeadBanks.beforeOutput_heads B i X sel base.val positions blocks old new
    f hf tape next m sub p v oldHeads sitesFit room
  have frame := ShrinkGeometryHeadBanks.beforeOutput_frame B i X sel base.val positions blocks old new
    next p v sitesFit room
  refine ⟨pre,selector,tail,gp,npre,empty,plogs,ppost,selectGroup,hin,stage,choices,logs,selectOut,
    selectOut.symm ▸ gt,ntail,?_,tailChoices,tailEvents,gfull,?_,?_,postFull,before.raw,beforeRows,beforePitch,
    afterHeader.raw,?_,afterHeader.entry.pitch,banks.1,banks.2,frame⟩
  · intro q hq bs hb
    have hmem : bs ∈ tail.flatMap (fun q => q.stage.choices) := List.mem_flatMap.mpr ⟨q,hq,hb⟩
    rw [tailChoices] at hmem
    exact (List.mem_replicate.mp hmem).2
  · rw [List.length_append,List.length_cons,npre,ntail]
  · simp only [List.flatMap_append,List.flatMap_cons,plogs,logs,ShrinkBranch.Selected.reports,
      eventLog,List.append_assoc] at tailEvents ⊢
    rw [tailEvents]
  · rw [← postFull]; exact (below_data gfull cells.1).trans rows

end CompressorRecords.ShrinkScheduledGeometry

end

end VPVNP
end Computability
end OAI
