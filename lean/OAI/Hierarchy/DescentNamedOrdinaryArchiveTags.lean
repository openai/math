import OAI.Hierarchy.DescentRegisteredFinalEvent
import OAI.Hierarchy.DescentDatePortTaggedRead
import OAI.Hierarchy.DescentOrdinaryAllPointerRows
import OAI.Hierarchy.DescentDatedOrdinaryRegisteredOperand

namespace OAI
/-! # All tagged rows on the history state returned by the registered ordinary date -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler Computability.VPVNP.BurstRAM PrivateRAM DescentPacking.PackedMatch.Local.Stage DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony DescentSIMDLookup
open DescentPriorOperandColumns DescentOrdinaryAtomFieldRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ}
    {C : Type*} (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position) (c : C) (mem : Memory w)

local notation "t" => (traces c)
local notation "code" => instruction (w:=w) traces b initial
variable {i z D z' D' : ℕ} {u : ℝ} {W : MarkedWorld F d P bits}
    {src : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {nrm : Normalize ((T.result he).state choice)}
    {dst : Reached nrm.result G q ε S k (i+1) z' D' wire hist}
    (before : Path (traces c).first src) (ticket : OrdinaryLink src he T choice nrm dst)
    (after : Path dst (traces c).last) (cut : (before.ordinary ticket).append after=(traces c).path)
local notation "evt" => (Path.Event.ordinary before ticket after cut)
local notation "at₀" => (calendar (w:=w) traces b initial i)
local notation "ports" => (at₀).ports
local notation "root₀" => (at₀).floor
local notation "ram" => DateCode.history code mem i
local notation "make" f:arg => f ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload
    (b.seats i) root₀ b.ordinary
local notation "v" => make DatePorts.ordinaryModel


variable (positive : 0<k) (room : DatePorts.OrdinaryCodeRoom (calendar (w:=w) traces b initial i).ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload (b.seats i) (calendar (w:=w) traces b initial i).floor b.ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom (calendar (w:=w) traces b initial i).ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload (b.seats i) (calendar (w:=w) traces b initial i).floor b.ordinary w (b.profile i) b.header room)
local notation "prog" => (make DatePorts.ordinaryDate) w (b.profile i) b.header positive room
local notation "next₀" => (⟨make DatePorts.ordinaryPorts,(v).fullEnd root₀⟩ : Position)
local notation "mv" => (⟨prog,next₀⟩ : Move w)
variable (fixed : ∀r : RunTrace.Events traces i, ∀y : Move w, issued traces b i r (calendar (w:=w) traces b initial i) y →
  y = ⟨DatePorts.ordinaryDate (calendar (w:=w) traces b initial i).ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload (b.seats i) (calendar (w:=w) traces b initial i).floor b.ordinary w (b.profile i) b.header positive room,
    ⟨DatePorts.ordinaryPorts (calendar (w:=w) traces b initial i).ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload (b.seats i) (calendar (w:=w) traces b initial i).floor b.ordinary, (DatePorts.ordinaryModel (calendar (w:=w) traces b initial i).ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload (b.seats i) (calendar (w:=w) traces b initial i).floor b.ordinary).fullEnd (calendar (w:=w) traces b initial i).floor⟩⟩)


local notation "oldAt" => (calendar (w:=w) traces b initial (i+1)).ports
local notation "floor" => (v).stageStart root₀
local notation "d₀" => DonorDate.atDate G S b.gain k i b.p
local notation "meter" => (d₀).counter b.payload (((d₀).schedule b.payload (b.seats i) (v).bitsPerField).rotationEnd (ports).io.roster floor) b.header
local notation "physical" => (make DatePorts.ordinaryWritten) w (b.profile i) b.header positive room exec ram

local notation "metadataAt" => (make DatePorts.ordinaryMetadata) w (b.profile i) b.header positive room exec ram
local notation "banks_" => (v).finalChart.out ((v).metaEnd floor)

set_option maxHeartbeats 1000000 in
include fixed before after cut in
omit [Fintype P] in
/-- All seven physical pages at the selected ordinary cut, including dormant rows. -/
theorem ordinary_history_tags («meta» : (v).MetaWords) (old : Books (v).resolver)
    (jobs : Fin (v).resolver.jobs→DescentDatedPriorOperand.Source (v).resolver)
    (newRead : ∀f x,Reads ((v).nodeChart.bank ((v).nodeBankBase floor) f x) («meta» f x)
      (v).resolver.lanes metadataAt)
    (spanRead : ∀x pg,Reads (previousBank (v).resolver ((v).vectorOutput floor) x pg)
      (old x pg) (v).resolver.lanes metadataAt)
    (keyRead : ∀j,Reads (Banks.wordBank (v).resolver ((v).normalizedEnd floor) j)
      (fun h g=>DescentPackedOperand.word ((jobs j).compiled h g)) (v).resolver.lanes metadataAt)
    (saved : (meter).endAddr≤banks_) (away : b.header<(meter).endAddr) :
    DatePorts.ArchiveTags oldAt (DateCode.history code mem (i+1)) :=by
  have output:= (v).written_pointer_rows «meta» old jobs floor room.result.operands
    (by rw [(v).after_end floor room.result.geometry];exact room.result.limit) metadataAt newRead spanRead keyRead
  have posted:=ordinary_posted_cut traces b initial c mem before ticket after cut positive room exec fixed
  let ps:=DatePorts.ordinary (v) floor
  have shape : ps.rangeLayout=(v).resolver := DatePorts.ordinary_range_layout (v) floor rfl rfl
  have atBase : ps.archive.arguments=banks_:=rfl
  rw [posted.2.1]
  change DatePorts.ArchiveTags ps _
  unfold DatePorts.ArchiveTags
  rw [atBase,shape]
  refine ⟨_,output.1.tags,?_⟩
  intro x pg posRow
  exact (ordinary_history_word traces b initial c mem before ticket after cut positive room exec fixed x pg
    (row _ _ _ posRow) saved away).trans (output.2 x pg posRow)

/-- The input to the final ordinary argument writer is its issued numerical metadata,
seven operand vectors, and resolved words at the observed date. -/
def OrdinaryTagWords : Prop :=
  (∀r : RunTrace.Events traces i,∀y : Move w,issued traces b i r at₀ y→y=mv) ∧
  (meter).endAddr≤banks_ ∧ b.header<(meter).endAddr ∧
  ∃(meta_ : (v).MetaWords) (old : Books (v).resolver)
    (jobs : Fin (v).resolver.jobs→DescentDatedPriorOperand.Source (v).resolver),
    (∀f x,Reads ((v).nodeChart.bank ((v).nodeBankBase floor) f x) (meta_ f x)
      (v).resolver.lanes metadataAt) ∧
    (∀x pg,Reads (previousBank (v).resolver ((v).vectorOutput floor) x pg)
      (old x pg) (v).resolver.lanes metadataAt) ∧
    ∀j,Reads (Banks.wordBank (v).resolver ((v).normalizedEnd floor) j)
      (fun h g=>DescentPackedOperand.word ((jobs j).compiled h g)) (v).resolver.lanes metadataAt

def OrdinaryTagSources : Prop :=
  ∃(pos : 0<k) (cash : (make DatePorts.OrdinaryCodeRoom) w)
    (run : (make DatePorts.OrdinaryExecutionRoom) w (b.profile i) b.header cash),
    OrdinaryTagWords traces b initial mem ticket pos cash run

include before after cut in
omit [Fintype P] in
theorem OrdinaryTagSources.result (live : i<final)
    (data : OrdinaryTagSources traces b initial mem ticket) :
    DatePorts.ArchiveTags oldAt (DateCode.history (RunTrace.machine traces (fun age _=>(code) age)) mem (i+1)) :=by
  obtain ⟨pos,cash,run,all⟩:=data
  obtain ⟨chosen,saved,away,meta_,old,jobs,issuedMeta,vectors,words⟩:=all
  rw [history_from_cuts traces b initial c mem (i+1) live]
  exact ordinary_history_tags traces b initial c mem before ticket after cut pos cash run chosen
    meta_ old jobs issuedMeta vectors words saved away

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
