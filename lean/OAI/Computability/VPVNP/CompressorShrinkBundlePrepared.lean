import OAI.Computability.VPVNP.CompressorShrinkBundlePackets
import OAI.Computability.VPVNP.CompressorShrinkBundleOperandSupport
import OAI.Computability.VPVNP.CompressorShrinkGreedyHeaderValues
import OAI.Computability.VPVNP.CompressorWindowPackets
import OAI.Computability.VPVNP.CompressorSourceGroups

/-!
# Preparing the eleven dense shrinking visits in the repeated block

The level header and table-zero pointer are read in each packet's actual
input memory. The greedy pass and preceding dense workers preserve these
cells, the scheduler row count, and the pitch below the scratch allocation.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkBundlePackets

open BurstRAM BlockPlanner Compression DescriptorSpace Schedule
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (exponent i) (packingLaneBits (exponent i) g)) (T : IncidenceDirectory w) (start : ℕ)
variable (base : Word w) (positions blocks t : ℕ)
local notation "script₀" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog (BlockProgram.script B))) base
local notation "first" => ((S.steps+1)*t)
local notation "st" => (levelStart L first : Word w)
local notation "H" => levelStart L 0
local notation "Pkt" => SourceWalk.Packet (SourceOnline.Visit script₀ w) w

/-- Chronological calendar ordinal of the first bundle packet in the indicated block repetition
and shrinking substep. -/
def startOrdinal := (script₀).initial.length+t*(script₀).block.length+(window B i).before.length

theorem startOrdinal_eq : startOrdinal B i t =
    (script₀).initial.length+t*(script₀).block.length+(BlockIndex.earlier B i).length+9 := by
  simp only [startOrdinal,window,List.length_append,Nat.add_assoc]
  rfl

/-- Read a dense visit's complete bank and launch its global worker at the
corresponding live directory row. -/
theorem prepared (j : Fin stages.length) (raw : Memory w) (rs : List (Report w))
    (header : ShrinkHeaderReads.Header i X T start L first raw)
    (rows : raw (pt).rows.val = (directoryRows L : Word w))
    (pitch : raw ((pt).directory-1).val = (levelWords L : Word w))
    (fit : (ShrinkInput.plan X start).stop < 2^w) (within : t < blocks) :
    SourceOnline.Prepared script₀ L base (startOrdinal B i t+j.val) (directoryRows L)
      ⟨visit B i X T start j,raw,rs⟩ := by
  let D := Window.operandRegion script₀ L base
  have lo : H ≤ levelStart L (first+i.val) := levelStart_mono L (Nat.zero_le _)
  have hfit : H < 2^w := lo.trans_lt ((Nat.le_add_right ..).trans_lt header.room)
  have entry : LevelFields.Entry L first (pt).data st raw := ⟨rfl,pitch⟩
  have values := field_values B i X T start j (header.reads B entry) fit
  have supp : HeaderOperands.Supported D (pt).data st raw ((script₀).visit (index B i j)) := by
    rw [index_visit]
    exact expr_reads B i header entry D (.inr (.inl rfl))
      (fun n _ ↦ .inr (.inr (lo.trans (Nat.le_add_right _ n)))) _
  let l := localIndex B i j
  let pos := (window B i).position l
  have live : (script₀).initial.length+t*(script₀).block.length+pos.val < directoryRows L := by
    rw [BlockProgram.directory_rows,(script₀).calendar_total]
    have h := Nat.mul_le_mul_right (script₀).block.length within
    rw [Nat.succ_mul] at h
    have hp := pos.isLt
    omega
  have ordinalEq : startOrdinal B i t+j.val = (script₀).initial.length+t*(script₀).block.length+pos.val :=
    Nat.add_assoc ..
  rw [ordinalEq]
  exact (window B i).prepared L base (BlockProgram.layout_arity ..).symm rfl hfit l t
    ⟨visit B i X T start j,raw,rs⟩ raw (fun _ _ ↦ rfl) rows pitch live
    ⟨rfl,values.1,values.2.1,values.2.2,supp.initial,supp.stop,supp.params⟩

/-- Every source packet sees the row total, immutable pitch and six incidence
heads from the published input header, through its own physical prefix of
worker writes. -/
theorem prepared_packets {m : Memory w} (r : ShrinkInput.Run X T start m)
    (header : ShrinkGreedyHeaderValues.Header i X T L first start (pt).data st m)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (fit : (ShrinkInput.plan X start).stop < 2^w) (within : t < blocks)
    (ps : List Pkt) (stagesEq : ps.map SourceWalk.Packet.stage = List.ofFn (visit B i X T start))
    (frame : ∀ p ∈ ps, ∀ x < start, p.input x = r.greedy.post x) (j : Fin ps.length) :
    SourceOnline.Prepared script₀ L base (startOrdinal B i t+j.val) (directoryRows L) ps[j.val] := by
  let p := ps[j.val]
  have len : ps.length = stages.length := by
    simpa only [List.length_map,List.length_ofFn] using congrArg List.length stagesEq
  let n := j.cast len
  have phase : p.stage = visit B i X T start n := by
    have he := congrArg (fun xs : List (SourceOnline.Visit script₀ w) ↦ xs[j.val]?) stagesEq
    change ps[j.val].stage = visit B i X T start ⟨j.val,n.isLt⟩
    simpa only [List.getElem?_map,List.getElem?_eq_getElem j.isLt,Option.map_some,
      List.getElem?_ofFn,dite_eq_left (show j.val < stages.length from n.isLt),Option.some.injEq] using he
  have same (x : ℕ) (hx : x < start) : p.input x = m x :=
    (frame p (List.getElem_mem ..) x hx).trans (r.greedy.below x hx)
  have hdr := header.keep_below same
  have lo := levelStart_mono L (Nat.zero_le (first+i.val))
  have room := header.raw.room
  have bounds := Window.lowCells (A := script₀) L base (BlockProgram.layout_arity ..).symm rfl
    (lo.trans_lt ((Nat.le_add_right ..).trans_lt room))
  have before := header.fieldsBelow
  have row := (same _ (bounds.1.trans (lo.trans_lt ((Nat.le_add_right ..).trans_lt before)))).trans rows
  have hp : (⟨visit B i X T start n,p.input,p.reports⟩ : Pkt) = p := by rw [← phase]
  have prep := prepared B i X T start base positions blocks t n p.input p.reports hdr.raw
    row hdr.entry.pitch fit within
  rw [hp] at prep
  exact prep

/-- The dense segment joins the greedy and term packet groups at its exact
directory offset and physical post-memory. -/
theorem group {m : Memory w} (r : ShrinkInput.Run X T start m) (abs : List (Report w))
    (last : ShrinkBundlePlan.AbsoluteRun r abs) (room : ShrinkInput.stop X start < 2^w)
    (low : ∀ c, H ≤ (T.column c).val) (within : t < blocks)
    (header : ShrinkGreedyHeaderValues.Header i X T L first start (pt).data st m)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (cap : ℕ) (clock : SourceOnline.scanCap script₀ (maxFuel B i) ≤ cap) :
    ∃ ps : List Pkt,
      SourceOnline.Group script₀ L base cap (startOrdinal B i t) (directoryRows L) r.greedy.post ps ∧
      ps.map SourceWalk.Packet.stage = List.ofFn (visit B i X T start) ∧
      ps.flatMap SourceWalk.Packet.reports = ShrinkBundlePlan.Scheduled.preparationReports X T start r ++ abs ∧
      SourceOnline.post r.greedy.post ps = after r.post (eventLog abs) := by
  obtain ⟨ps,labels,logs,chron,checks,final⟩ := packets B i X T start L cap clock r abs last room low
  have fit := (ShrinkInput.range_bounds X start).2.2.2.trans_lt room
  exact ⟨ps,⟨chron,fun p hp ↦ (checks p hp).1,
    prepared_packets B i X T start base positions blocks t r header rows fit within ps labels
      (fun p hp ↦ (checks p hp).2)⟩,labels,logs,final⟩

/-- The repeated online block executes the eleven dense workers, retaining
their reports and branch tapes and ending at the absolute-ID post-memory
throughout the data suffix. -/
theorem interval {m : Memory w} (r : ShrinkInput.Run X T start m) (abs : List (Report w))
    (last : ShrinkBundlePlan.AbsoluteRun r abs) (room : ShrinkInput.stop X start < 2^w)
    (low : ∀ c, H ≤ (T.column c).val) (within : t < blocks)
    (header : ShrinkGreedyHeaderValues.Header i X T L first start (pt).data st m)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (cap : ℕ) (clock : SourceOnline.scanCap script₀ (maxFuel B i) ≤ cap) (live : Memory w)
    (data : SourceTransport.Agree (H ≤ ·) r.greedy.post live)
    (atRow : (live (pt).ordinal.val).val = startOrdinal B i t)
    (total : (live (pt).rows.val).val = directoryRows L)
    (tag : live (pt).tag.val = LiveStageLink.tagWord w (Online.calendarIndex (script₀).size (script₀).size))
    (pitch : live ((pt).directory-1).val = (levelWords L : Word w)) :
    ∃ ss : List (Online.Run.Step (script₀).size (script₀).size w),
      Online.Run.Interval (script₀).plan pt cap live ss ∧
      ss.map Online.Run.Step.phase = List.ofFn (index B i) ∧
      ss.flatMap (fun s ↦ s.row.reports) = ShrinkBundlePlan.Scheduled.preparationReports X T start r ++ abs ∧
      ss.map (fun s ↦ s.row.choices) = List.ofFn (fun j ↦ (visit B i X T start j).choices) ∧
      let post := Online.Run.finalMemory (C := (script₀).catalog) pt live ss
      SourceTransport.Agree (H ≤ ·) (after r.post (eventLog abs)) post ∧
      (post (pt).ordinal.val).val = startOrdinal B i t+11 ∧ post (pt).rows.val = live (pt).rows.val ∧
      post ((pt).directory-1).val = live ((pt).directory-1).val ∧
      SourceBankFrame.Stable (base.val+6) live (Online.Run.intervalLog (script₀).plan pt live ss) := by
  obtain ⟨ps,grp,labels,logs,final⟩ :=
    group B i X T start base positions blocks t r abs last room low within header rows cap clock
  have hfit := (levelStart_mono L (Nat.zero_le (first+i.val))).trans_lt
    ((Nat.le_add_right ..).trans_lt header.raw.room)
  have len : ps.length = stages.length := by
    simpa only [List.length_map,List.length_ofFn] using congrArg List.length labels
  have bound : startOrdinal B i t+ps.length ≤ directoryRows L := by
    rw [BlockProgram.directory_rows,(script₀).calendar_total,startOrdinal,len,stages]
    have block := congrArg List.length (window B i).block
    simp only [List.length_append,entries,List.length_map] at block
    have steps := Nat.mul_le_mul_right (script₀).block.length within
    rw [Nat.succ_mul] at steps
    omega
  obtain ⟨ss,actual,phases,reports,choices,agree,done,sameRows,samePitch,stable⟩ :=
    SourceOnline.interval_stable script₀ L base (BlockProgram.layout_arity ..).symm rfl hfit cap
      (startOrdinal B i t) (directoryRows L) live r.greedy.post ps grp.chronological
      grp.checked grp.prepared bound le_rfl data atRow total tag pitch
  refine ⟨ss,actual,?_,?_,?_,final ▸ agree,done.trans (congrArg (startOrdinal B i t+·) len),sameRows,samePitch,stable⟩
  · apply phases.trans
    change ps.map (fun p ↦ p.stage.phase) = List.ofFn (fun j ↦ (visit B i X T start j).phase)
    simpa only [List.map_map,List.map_ofFn,Function.comp_def] using
      congrArg (List.map SourceOnline.Visit.phase) labels
  · change (ss.map (fun s ↦ s.row.reports)).flatten = _
    rw [reports]; exact logs
  · apply choices.trans
    simpa only [List.map_map,List.map_ofFn,Function.comp_def] using
      congrArg (List.map SourceOnline.Visit.choices) labels

end CompressorRecords.ShrinkBundlePackets

end

end VPVNP
end Computability
end OAI
