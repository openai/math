import OAI.Hierarchy.TaggedWideCalendarDateWords
import OAI.Hierarchy.TaggedWireFundedPreclipWidth
import OAI.Hierarchy.TaggedWideCarriedCast
import OAI.Hierarchy.TaggedWirePacketNeighborMetadata

namespace OAI
/-! # The physical signed-output and spill-input words of a chosen preclip state -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor WireTelescope AdaptiveProbe ReportSockets
open Tagged PassiveWindow Tagged.WideStack Tagged.WideControlJoin
open ProtocolRAM.Calendar Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
set_option cleanup.letToHave false
set_option Elab.async false

variable {h W k attempts n cap : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k attempts) (unique : Exclusive marks)
    (order : Fin n≃Source S π depth marks) (bits : Fin n→ℕ)
    (capacity : Public S h W k attempts→ℕ)
    (fit : ∀i side,bits i≤capacity (named S π depth marks unique order (i,side)))
    (within : ∀r,capacity r≤cap)
local notation "K" => siteLast h (2^W) k+1
local notation "degree" => stride k S.degree attempts
local notation "ends" => sorted S π depth marks ∘ order
local notation "port" => named S π depth marks unique order
local notation "slot" => shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S
local notation "whereAt" => named_coordinate S π depth marks unique order
variable {B : Widths K} (eqn : installedWidths ends bits=B) (s : Fin K) (x : State B s)
local notation "bounds" => fun i=>(fit i false).trans (within _)
local notation "seat" => PacketNeighbor.localSlot ends bits port slot whereAt s
local notation "parts" => carried ends bits s bounds seat eqn
local notation "layout" => placedMiddle S π depth marks unique order bits capacity fit within eqn
local notation "site" => placedMiddle_site S π depth marks unique order bits capacity fit within eqn
local notation "selected" => LedgerStep.siteChart layout site s
local notation "mid" => LedgerStep.middle s selected x

theorem middle_carried_bits : ∀i p,(parts).owner i=some p→∀u : Fin ((parts).width i),
    mid (finProdFinEquiv (i,u.castLE ((parts).within i)))=(x p).val.testBit ((parts).base i+u.val) := by
  subst B
  let lay:=placedMiddle S π depth marks unique order bits capacity fit within rfl
  let each:=placedMiddle_site S π depth marks unique order bits capacity fit within rfl
  let sl:=LedgerStep.siteChart lay each s
  let data:=LedgerStep.middle s sl x
  apply carried_reads ends bits s bounds seat rfl x (fun i u=>data (finProdFinEquiv (i,u)))
  intro a u
  let bb : (bitGraph (rowGraph ends) bits).Port s:=⟨(⟨a.val.val.1,u⟩,a.val.val.2),a.val.property⟩
  let arg:=NamedAperture.atPort ends bits bb
  have loc : sl arg=finProdFinEquiv (seat a,u.castLE (bounds _)) := by
    change (LedgerStep.rolesChart capacity within slot
      (NamedAperture.place ends bits port capacity fit ⟨s,NamedAperture.atPort ends bits bb⟩)).2=_
    rw [NamedAperture.port_read]
    rfl
  exact ((congrArg (LedgerStep.middle s sl x) loc.symm).trans
    (LedgerStep.middle_at s sl x arg)).trans (NamedAperture.rowBits_siteBits ends bits x bb).symm

variable {Ex Se D : Type} (G : Gate) (es : List Event)
    (timelineCapacity : Public S h W k attempts→ℕ)
    (wire : Fin ((es.length+1)*Fintype.card ((r:Public S h W k attempts)×Fin (timelineCapacity r)))→D)
    (day : Fin es.length) (ext : Ex→Bool) (sel : Se→Bool) (data : D→Bool) (m : Memory G.W)
local notation "ev" => Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim data mid) (G.terminal m)))

theorem substep_middle_carried_bits (clip : Bool) :
    ∀i p,(parts).owner i=some p→∀u : Fin ((parts).width i),
      Sum.elim ev id (LedgerStep.substepWord G es timelineCapacity slot wire day s clip (!clip) i (u.castLE ((parts).within i)))=
        (x p).val.testBit ((parts).base i+u.val) := by
  intro i p occupied u
  exact (LedgerStep.substepWord_middle G es timelineCapacity slot wire day s ext sel data m mid clip i
    (u.castLE ((parts).within i))).trans
    (middle_carried_bits S π depth marks unique order bits capacity fit within eqn s x i p occupied u)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
set_option cleanup.letToHave false
set_option Elab.async false
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h


local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "f" => v.nativeFormats P h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "order" => wideRouteOrder h D k


variable (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h D) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows

local notation "funded" => v.wideFundedRaw h width v.maxBits seed
local notation "original" => v.wideSignedWords h width stock v.radius π.symm order funded
local notation "V" => v.catalystMarkets P h width
local notation "dims" => v.wide_stock_sizes h width age budget small
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open Filter CalendarTape RepairHistogram HistoryRoles.RoleProgram ProtocolRAMEmit
open LinearAlgebra.SpectralBooks ChordGraph
namespace FundedDate
variable {v h width size π seed age budget small} {tail x} {a : Attempt}
    {t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x} {c : (slots (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
local notation "ev" => Event.attempt a
local notation "u" => (es).length-(ev::tail).length
local notation "native" => origin H.code
local notation "tape" => v.wideFundedRaw h width v.maxBits ((L).header es H.code seed)
local notation "entry" => run C H.prior native
local notation "out" => after C ev entry
local notation "t₀" => v.taskCommit P h width a
local notation "st" => v.stage P h width r banks source table target owners a entry
local notation "tag" => RepairHistogram.kind («goods»:=(t₀).goods) (t₀).plan.bank (t₀).columns st
local notation "o" => v.nativeSlots P h width a
local notation "inputGoods" => fun i=>v.wireGoodsAt h width u x ((o).symm i)
local notation "ar" => ((f) a).pricedArea
local notation "axes" => Columns h D×Fin k
local notation "supply" => fuel v.mesh*width
local notation "origReserve" => fun pair=>supply-v.wireUsedAt h width u x pair

local notation "place" => siteNumber h D k
local notation "paid0" => v.wirePaidAt h width v.maxBits u x
local notation "oldMount" => (P).catalogue.coreMount π.symm place (v.wideOrder h width) x
local notation "afterValue" => Sum.elim H.afterPaid (Sum.elim (H.afterGoods ∘ o) H.nextReserve)
local notation "leftover" => fun z=>(origReserve) z-H.reserveDebit z
local notation "carry" => (oldMount).actual.chordWidths paid0+H.afterMount.actual.chordWidths H.paid+
  (catalystGraph place).chordWidths leftover
local notation "cap" => (show FeedTransfer.Transfer h D k from
  ⟨fun _=>0,fun i=>H.afterGoods ((o) i)+H.spill ((o) i),fun _=>0,fun i=>H.afterGoods ((o) i),
    fun i=>H.spill ((o) i),fun _=>by simp⟩)

local notation "rawOf" J:arg => (L).header es (FundedDate.code J) seed
open private preclipEntriesAt from OAI.Hierarchy.TaggedWireFundedPreclipWidth

open HistoryRoles
variable (J : v.FundedDate h width size π seed age budget small t c)
    (expanse : v.wideFundedSize h width v.maxBits≤ size)
    (ledgerAge : v.wideDatedLedgerHeight≤h) (reportAge : v.reportHeight≤h)
    (paidAge : v.paidBallotHeight≤h) (word : v.ReportWordRoom h width)
    (first : ℕ) (input : Fin (es).length→Memory w)
local notation "cc" => (P).catalogue
local notation "nativeJ" => origin J.code
local notation "archive" => checkedOut C ((A).endAddress v.mesh) nativeJ
local notation "terms" => preclipEntriesAt (v:=v) (h:=h) (width:=width) (size:=size) (π:=π) (rawOf J) expanse ledgerAge small budget (0 : Word w)
local notation "marked" => v.birthMarks P h width r banks source table target owners nativeJ
local notation "nativeOrder" => v.wideOrder h width
local notation "cardRows" => v.wide_dated_bought_rows h width
local notation "axis" => pairKeys (Columns h D) k
local notation "names" => timeRows v.sampler π.symm v.depth marked cc nativeOrder cardRows axis
local notation "address" => DatedRows.embed v.sampler π.symm v.depth marked cc nativeOrder cardRows
local notation "directions" => HistoryRoles.sorted v.sampler π.symm v.depth marked
local notation "correctedWidths" => v.wideCorrectedWidths h width size v.radius π.symm (rawOf J) v.maxBits terms first input
local notation "clip" => fun i=>RouteSettlement.actual (v.wideSpillPage h width v.maxBits first J.index.val).overflow
  (input J.index) (PurchaseInventory.slot i)

local notation "rows" => (correctedWidths 0 J.index.succ) ∘ address ∘ names
local notation "bound" => FeedTransfer.input (π:=π.symm) («place»:=place) carry cap
variable (archived : ∀addr<(A).endAddress v.mesh,input J.index addr=archive addr)
    (unique : Exclusive marked) (capacity : Public v.sampler h v.W k v.wideJobs→ℕ)
    (fit : ∀i side,(rows) i≤capacity (named v.sampler π.symm v.depth marked unique names (i,side)))
    {length : ℕ} (within : ∀portName,capacity portName≤length)
local notation "proof" => H.indexed_middle_width J expanse ledgerAge reportAge paidAge word first input archived

local notation "layout" => H.preclip_indexed_layout J expanse ledgerAge reportAge paidAge word first input
  archived unique capacity fit within


open PassiveWindow Tagged.WideStack Tagged.WideControlJoin Calendar
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
local notation "pos" => H.preclip_indexed_site J expanse ledgerAge reportAge paidAge word first input
  archived unique capacity fit within
local notation "ends" => directions ∘ names
local notation "ports" => named v.sampler π.symm v.depth marked unique names
local notation "socket" => shelfSlot (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "here" => named_coordinate v.sampler π.symm v.depth marked unique names
variable (siteId : Fin (siteLast h D k+1)) (state : State bound siteId)
local notation "parts" => carried ends rows siteId (fun i=>(fit i false).trans (within _))
  (PacketNeighbor.localSlot ends rows ports socket here siteId) proof
local notation "mid" => LedgerStep.middle siteId (LedgerStep.siteChart layout pos siteId) state
variable {Ex Se Data : Type} (gate : Gate)
    (timelineCapacity : Public v.sampler h v.W k v.wideJobs→ℕ)
    (wire : Fin (((es).length+1)*Fintype.card ((portName : Public v.sampler h v.W k v.wideJobs) × Fin (timelineCapacity portName)))→Data)
    (ext : Ex→Bool) (sel : Se→Bool) (data : Data→Bool) (mem : Memory gate.W)

-- Assemble the actual funded instance of the generic port equation with all indices visible.
open Lean Elab Term in
local elab "nativePortReading" "[" termsIn:term,* "]" : term => do
  let mut args := #[]
  for t in termsIn.getElems do
    args := args.push (← elabTerm t none)
  let constant ← Meta.mkConstWithFreshMVarLevels ``substep_middle_carried_bits
  return mkAppN constant args

-- The installed layout and the transported layout describe the same funded state.
open Lean Elab Tactic in
local elab "exactPortReading " sourceLaw:ident : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let result ← Meta.getFVarFromUserName sourceLaw.getId
    goal.assign result
    replaceMainGoal []

/-- The two physical substeps of the selected attempt see the given
intermediate state on the original corrected widths and role ordering. -/
theorem preclip_indexed_carried (clipSide : Bool) :
    let aug:=Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim data mid) (gate.terminal mem)))
    ∀i p,(parts).owner i=some p→∀offset : Fin ((parts).width i),
      Sum.elim aug id (LedgerStep.substepWord gate es timelineCapacity socket wire J.index siteId clipSide (!clipSide) i
        (offset.castLE ((parts).within i)))=(state p).val.testBit ((parts).base i+offset.val) := by
  let observed := nativePortReading [h, v.W, k, v.wideJobs,
    Fintype.card (HistoryRoles.Source v.sampler π.symm v.depth marked), length,
    v.sampler, π.symm, v.depth, marked, unique, names, rows, capacity, fit, within,
    bound, proof, siteId, state, Ex, Se, Data, gate, es, timelineCapacity,
    wire, J.index, ext, sel, data, mem, clipSide]
  exactPortReading observed

theorem preclip_indexed_carried_at (day : Fin (es).length) (dated : J.index=day) (clipSide : Bool) :
    let aug:=Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim data mid) (gate.terminal mem)))
    ∀i p,(parts).owner i=some p→∀offset : Fin ((parts).width i),
      Sum.elim aug id (LedgerStep.substepWord gate es timelineCapacity socket wire day siteId clipSide (!clipSide) i
        (offset.castLE ((parts).within i)))=(state p).val.testBit ((parts).base i+offset.val) := by
  subst day
  let observed := H.preclip_indexed_carried J expanse ledgerAge reportAge paidAge word first input
    archived unique capacity fit within siteId state gate timelineCapacity wire ext sel data mem clipSide
  exactPortReading observed

theorem preclip_indexed_offer_read (day : Fin (es).length) (dated : J.index=day) (clipSide : Bool)
    (active : Widths (siteLast h D k+1)) (atWidth : installedWidths ends rows=active) :
    let carrying :=carried ends rows siteId (fun i=>(fit i false).trans (within _))
      (PacketNeighbor.localSlot ends rows ports socket here siteId) atWidth
    let y:=cast (congrArg (fun U=>State U siteId) ((proof).symm.trans atWidth)) state
    let aug:=Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim data mid) (gate.terminal mem)))
    ∀i p,carrying.owner i=some p→∀offset : Fin (carrying.width i),
      Sum.elim aug id (LedgerStep.substepWord gate es timelineCapacity socket wire day siteId clipSide (!clipSide) i
        (offset.castLE (carrying.within i)))=(y p).val.testBit (carrying.base i+offset.val) := by
  let observed := H.preclip_indexed_carried_at J expanse ledgerAge reportAge paidAge word first input
    archived unique capacity fit within siteId state gate timelineCapacity wire ext sel data mem day dated clipSide
  let shifted := carried_cast_read ends rows siteId (fun i=>(fit i false).trans (within _))
    (PacketNeighbor.localSlot ends rows ports socket here siteId) proof state
    (fun i offset=>Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim (Sum.elim data mid) (gate.terminal mem)))) id
      (LedgerStep.substepWord gate es timelineCapacity socket wire day siteId clipSide (!clipSide) i offset))
    observed ((proof).symm.trans atWidth)
  exactPortReading shifted

-- The dependent physical layouts are too large for the optional premise-suggestion index.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "preclip_indexed_carried"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "preclip_indexed_carried_at"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "preclip_indexed_offer_read"
end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
