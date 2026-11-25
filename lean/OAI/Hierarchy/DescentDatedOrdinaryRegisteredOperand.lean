import OAI.Hierarchy.DescentDatedOrdinaryPostedCut

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

local notation "A" => (base).registeredEntry prior floor
local notation "match₀" => (base).registered_match prior floor (Nat.le_max_left prior.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry prior floor
local notation "B" => (v).reachedSources floor

variable (w : ℕ) (shelf header : ℕ) (pos : 0<k)
variable (room : OrdinaryCodeRoom prior ticket op gain tail p f drift degree payload seats root ordinary w)
local notation "steps" => (v).issuedSteps root prior (A) room.signed w (match₀) (sh) room.blocks room.paths
  room.slots room.chip room.endFit room.packed room.radix room.funded


local notation "digits" => (v).signedInput floor room.signed
local notation "date₀" => DonorDate.atDate G S gain k i p

variable (exec : OrdinaryExecutionRoom prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header room)
local notation "opOut" => (v).argumentsAfter floor room.result.operands
  (by rw [(v).after_end floor room.result.geometry]; exact room.result.limit)

/-- The operand write on the native ordinary instruction, before its later primitive and counting passes. -/
def ordinaryWritten (m : Memory w) : Memory w :=
  (opOut).image ((v).beforeArgumentWrite root shelf header prior.io prior.archive.count digits (B) steps date₀ pos exec m)

/-- The state after the ordinary return has printed its two metadata pages. -/
def ordinaryMetadata (m : Memory w) : Memory w :=
  (v).beforeArgumentWrite root shelf header prior.io prior.archive.count digits (B) steps date₀ pos exec m

theorem registered_blocks_groups : 2^(v).venue.k=(v).resolver.blocks ∧ (v).venue.groups=(v).resolver.groups :=
  ⟨rfl,rfl⟩


open DescentDatedPriorOperand DescentOperandStateBanks
local notation "meter" => (date₀).counter payload (((date₀).schedule payload seats (v).bitsPerField).rotationEnd prior.io.roster floor) header

theorem ordinary_output_word (m : Memory w) (x : Fin (v).resolver.blocks) (p₀ : Pages (v).resolver.operands)
    (row : Fin (v).resolver.rows) (saved : (meter).endAddr≤(v).finalChart.out ((v).metaEnd floor))
    (away : header<(meter).endAddr) :
    let address := (previousBank (v).resolver ((v).finalChart.out ((v).metaEnd floor)) x p₀).base+row.val
    ordinaryOutput prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m address=
    ordinaryWritten prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m address :=
  (v).date_argument_word root shelf header prior.io prior.archive.count digits (B) steps room.result date₀ pos exec m x p₀ row saved away

/-- The original meter ends before the metadata shelves allocated in the return phase. -/
theorem ordinary_metadata_saved (paid : (meter).endAddr≤(v).donorEnd floor) :
    (meter).endAddr≤(v).nodeChart.output ((v).nodeBankBase floor):=by
  have previous : (v).donorEnd floor≤(v).endAddress floor:=by
    have norms:=(v).arguments_extent floor
    change (v).normalizedEnd floor=(v).vector.endAddress ((v).donorEnd floor)+(v).argumentExtra at norms
    rw [DescentOperandVectorArena.affine (v).vector _] at norms
    change _≤(v).resolver.endAddress ((v).normalizedEnd floor)
    rw [(v).resolver.affine]
    omega
  have raster:(v).endAddress floor≤(v).rasterEnd floor:=by
    rw [PhysicalOrdinary.rasterEnd,StageVenueTail.OrdinaryRaster.translated]
    exact Nat.le_add_right ..
  have venue:=(v).venue.order ((v).rasterEnd floor)
  have ready:(v).rasterEnd floor≤(v).metaStart floor:=
    venue.1.trans (venue.2.1.trans (venue.2.2.1.trans venue.2.2.2))
  let c:=(v).nodeChart
  let cut:=c.digitEnd ((v).metaStart floor) ((v).resolver.size+2)
  have fromStart:(v).metaStart floor≤cut:=Nat.le_add_right ..
  have inputs:cut≤(v).nodeBankBase floor:=Nat.le_add_right ..
  have cells:(v).nodeBankBase floor≤c.scalarEnd ((v).nodeBankBase floor):=Nat.le_add_right ..
  have out:c.scalarEnd ((v).nodeBankBase floor)≤c.output ((v).nodeBankBase floor):=Nat.le_add_right ..
  exact paid.trans (previous.trans (raster.trans (ready.trans (fromStart.trans (inputs.trans (cells.trans out))))))

/-- Later writes of the same date preserve each row of each printed metadata page. -/
theorem ordinary_output_metadata (m : Memory w) (f₀ : Fin 2) (x : Fin (v).resolver.blocks)
    (cells : Fin (v).resolver.hosts→Fin (v).resolver.groups→Cell ((v).nodeChart.bits*(v).resolver.nodes))
    (observed : Reads ((v).nodeChart.bank ((v).nodeBankBase floor) f₀ x) cells (v).resolver.lanes
      (ordinaryMetadata prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m))
    (saved : (meter).endAddr≤(v).nodeChart.output ((v).nodeBankBase floor)) (away : header<(meter).endAddr) :
    Reads ((v).nodeChart.bank ((v).nodeBankBase floor) f₀ x) cells (v).resolver.lanes
      (ordinaryOutput prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m):=by
  intro posRow
  let bank:=(v).nodeChart.bank ((v).nodeBankBase floor) f₀ x
  let address:=bank.base+(row _ _ _ posRow).val
  have stop:(v).nodeChart.endAddress ((v).nodeBankBase floor)=(v).metaEnd floor:=
    (v).nodeEnd floor room.result.chart room.result.digit
  have before:(v).metaEnd floor≤(v).operandEnd floor:=by
    rw [PhysicalOrdinary.operandEnd,(v).operandBook.affine]
    exact Nat.le_add_right ..
  have boundary:=(v).nodeChart.valid ((v).nodeBankBase floor)
    ((stop.le.trans before).trans_lt room.result.limit) f₀ x
  have bound : address<(v).metaEnd floor:=by
    have place:=Nat.add_lt_add_left ((row _ _ _ posRow).isLt.trans_le boundary.2) bank.base
    exact place.trans_le (boundary.1.2.2.trans stop.le)
  have savedAt:(meter).endAddr≤address:=by
    have lower:(v).nodeChart.output ((v).nodeBankBase floor)≤bank.base:=Nat.le_add_right ..
    exact saved.trans (lower.trans (Nat.le_add_right ..))
  have printed:=(v).date_argument_read root shelf header prior.io prior.archive.count digits (B) steps room.result
    date₀ pos exec m address (bound.trans_le before) savedAt (Nat.ne_of_gt (away.trans_le savedAt))
  have heldPages:=(v).argumentsAfter_any floor room.result.operands
    (by rw [(v).after_end floor room.result.geometry];exact room.result.limit)
    (ordinaryMetadata prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m)
  exact printed.trans ((heldPages.2 address (.inl bound)).trans (observed posRow))

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology


namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler Computability.VPVNP.BurstRAM PrivateRAM DescentPacking.PackedMatch.Local.Stage DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony DescentSIMDLookup
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
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

set_option maxHeartbeats 1000000 in
include fixed before after cut in
omit [Fintype P] in
theorem ordinary_history_word (x : Fin (v).resolver.blocks) (p₀ : Pages (v).resolver.operands)
    (row : Fin (v).resolver.rows) (saved : (meter).endAddr≤(v).finalChart.out ((v).metaEnd floor))
    (away : b.header<(meter).endAddr) :
    let address := (previousBank (v).resolver ((v).finalChart.out ((v).metaEnd floor)) x p₀).base+row.val
    DateCode.history code mem (i+1) address=physical address :=by
  intro address
  rw [(ordinary_posted_cut traces b initial c mem before ticket after cut positive room exec fixed).2.2]
  exact (make DatePorts.ordinary_output_word) w (b.profile i) b.header positive room exec ram x p₀ row saved away


set_option maxHeartbeats 1000000 in
include fixed before after cut in
omit [Fintype P] in
theorem ordinary_history_metadata (f₀ : Fin 2) (x : Fin (v).resolver.blocks)
    (cells : Fin (v).resolver.hosts→Fin (v).resolver.groups→Cell ((v).nodeChart.bits*(v).resolver.nodes))
    (read : Reads ((v).nodeChart.bank ((v).nodeBankBase floor) f₀ x) cells (v).resolver.lanes
      ((make DatePorts.ordinaryMetadata) w (b.profile i) b.header positive room exec ram))
    (saved : (meter).endAddr≤(v).nodeChart.output ((v).nodeBankBase floor)) (away : b.header<(meter).endAddr) :
    Reads ((v).nodeChart.bank ((v).nodeBankBase floor) f₀ x) cells (v).resolver.lanes
      (DateCode.history code mem (i+1)):=by
  rw [(ordinary_posted_cut traces b initial c mem before ticket after cut positive room exec fixed).2.2]
  exact (make DatePorts.ordinary_output_metadata) w (b.profile i) b.header positive room exec ram f₀ x cells read saved away

open DescentKernelHistory DescentCompiler DescentRetainedRangeDigits DescentLocalArchiveOrder
variable (description : BitDescription nrm.result)
    (order : ∀y,(description.recipe y).Node≃Fin (Fintype.card (description.recipe y).Node))
    (capacity : ∀y,Fintype.card (description.recipe y).Node≤((calendar (w:=w) traces b initial (i+1)).ports).nodes)
    (hosts : ∀y,(Reached.NodeCells.coordinate dst y).1.val<((calendar (w:=w) traces b initial (i+1)).ports).operandHosts)
    (groups : S.groupCount (i+1)=((calendar (w:=w) traces b initial (i+1)).ports).venue.groups) (radix : k=((calendar (w:=w) traces b initial (i+1)).ports).venue.k)
    (lanes : 0<((calendar (w:=w) traces b initial (i+1)).ports).operandLanes)

set_option maxHeartbeats 1000000 in
include fixed before after cut in
omit [Fintype P] in
theorem ordinary_registered_operand (saved : (meter).endAddr≤(v).finalChart.out ((v).metaEnd floor))
    (away : b.header<(meter).endAddr) :
    DatePorts.rangeRegister oldAt dst description order capacity hosts groups radix lanes (DateCode.history code mem (i+1))=
      DatePorts.rangeRegister oldAt dst description order capacity hosts groups radix lanes physical :=by
  have portsAt := (ordinary_posted_cut traces b initial c mem before ticket after cut positive room exec fixed).2.1
  unfold DatePorts.rangeRegister
  apply fromRAM_frame
  rw [portsAt]
  intro x p₀ row
  exact ordinary_history_word traces b initial c mem before ticket after cut positive room exec fixed x p₀ row saved away

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
