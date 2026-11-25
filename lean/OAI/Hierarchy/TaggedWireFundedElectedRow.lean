import OAI.Hierarchy.TaggedWireFundedDate
import OAI.Hierarchy.TaggedWireFundedPacketWord
import OAI.Hierarchy.ProbeFixedElectedSource
import OAI.Hierarchy.ProbeFixedReadbackProducer

namespace OAI
/-! # The actual elected packet installation for every row of a funded prefix -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open PurchaseStage WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "boards" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger boards v.mesh (P).catalogue (P).routes F A)
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


variable (size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h (2^v.W)) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "mid" => v.wideSignedMidAt h width size stock M π order

local notation "funded" => v.wideFundedRaw h width v.maxBits seed
local notation "original" => v.wideSignedWords h width stock v.radius π.symm order funded
local notation "V" => v.catalystMarkets P h width
local notation "input" => fun _ : Equiv.Perm (Row h)=>original
local notation "dims" => v.wide_stock_sizes h width age budget small
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open StripDirectory
local notation "slab" => v.slab (v.seed P h width) P width

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option cleanup.letToHave false
private theorem committedFromValid {wordWidth labels copiesCount : ℕ} (ticket : Batch labels copiesCount)
    (state : Memory wordWidth) (pos : Word wordWidth) (on : ticket.selected state pos)
    (valid : ticket.valid state pos) : RepairHistogram.committed ticket state pos := by
  refine ⟨on, ?_⟩
  simpa only [Batch.valid, ite_eq_left on] using valid

namespace FundedDate
variable {v h width size π seed age budget small}
variable {a : Attempt} {tail : List Event} {x : Memory (Native.wordBits h (2^v.W) Native.copies)}
  {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt a::tail) x} {c : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}
  (H : v.FundedDate h width size π seed age budget small t c)
local notation "initial" => origin H.code
local notation "entry" => run C H.prior initial
local notation "snap" m => HistogramShelf.snapshot C a m
local notation "batch" => enabledBatch ((C).layout a) (repair C a)

theorem ballot (extent : (A).endAddress v.mesh≤ size) (j : Fin ((C).layout a).candidates) :
    let reg : Word w := (j.val:Word w)
    (batch).packet.eval (snap x) reg=(batch).packet.eval (snap entry) reg ∧
    (batch).termCount.read (snap x) ((batch).packet.eval (snap x) reg)=
      (batch).termCount.read (snap entry) ((batch).packet.eval (snap entry) reg) ∧
    ((batch).selected (snap x) reg↔(batch).selected (snap entry) reg) := by
  have cuts := (v.wide_funded_cuts h width size extent π seed age budget small t).1
  have left := cuts.choose_spec.choose_spec
  let coreStart:=CoreCatalogue.top h v.W (WideMemory.K h v.W) (WideMemory.dir h v.W k v.wideJobs).groups
    (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
  have last:=(Public.borders v.sampler coreStart h v.W k v.wideJobs v.depth).2
  have dir : (stratumHeader h D k v.sampler.degree v.depth ((P).routes.directory.keysBase)).stop≤(P).joint.initial :=
    last.trans ((Nat.le_add_right ..).trans (v.wideGeometryPrefix h width).2.2)
  have hfit : h<2^w := (Nat.lt_two_pow_self (n:=h)).trans (v.date_prefix_fit h)
  have cap : v.menu.maximum<2^w :=
    (((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (dims).market)).trans_lt hfit)
  have tables:=v.election_pages P h width a cap (dims).words.cut dir
  have wide : 4≤2^w:=calc
    4=2^2:=by decide
    _≤2^w:=Nat.pow_le_pow_right (by decide) (by unfold Native.wordBits; omega)
  have occ : Event.attempt a ∈ es := by
    have eqn : es = H.prior ++ .attempt a :: tail := H.cut.events
    rw [eqn]
    simp
  have fits : (A).base v.mesh (.attempt a)<2^w:=
    (Nat.le_add_right ..).trans_lt (((A).within v.mesh _ occ).trans_lt (dims).words.addresses)
  exact Slab.ballot_before slab boards F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
    (P).catalogue banks source table target owners a x entry H.before left.currentReady H.cut.currentReady wide fits tables j

theorem committed_at (extent : (A).endAddress v.mesh≤ size) (i : Fin ((C).layout a).candidates)
    (on : (batch).selected (snap x) (i.val:Word w)) :
    RepairHistogram.committed (batch) (snap entry) (i.val:Word w) := by
  have selected:=(H.ballot extent i).2.2.mp on
  exact committedFromValid _ _ _ selected ((H.cut.accepted_at H.valid) i.val i.isLt)

local notation "marks" => v.birthMarks P h width r banks source table target owners initial
local notation "ends" => (P).catalogue.physicalEnds (π:=π.symm) («marks»:=marks) (P).routes.directory (v.wideOrder h width) rfl
local notation "co" => checkedOut C ((A).endAddress v.mesh) initial
local notation "count" => Fintype.card (Columns h D)
variable [Nonempty (Fin k)]
private abbrev electedReadback := v.ReadbackRun P h width r banks source table target owners π.symm initial initial

variable (boxed : electedReadback H)
  (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size)
  (catRoom : (v.widePlacement h width).catalogue.rows < 2^(Native.wordBits h (2^v.W) Native.copies))
  (cols : Fintype.card (Columns h (2^v.W)) ≤ 2^(Native.wordBits h (2^v.W) Native.copies))
  (stages : Stages h (2^v.W) ≤ 2^(Native.wordBits h (2^v.W) Native.copies))
  (degree : v.sampler.degree ≤ 2^(Native.wordBits h (2^v.W) Native.copies))

include boxed extent catRoom cols stages degree in
def electedSource (i : Fin ((C).layout a).candidates) (hit : (batch).selected (snap x) (i.val:Word w)) :
    v.ElectedSource h width π.symm marks ends co a i.val := by
  let raw:=v.wideFundedRaw h width v.maxBits ((L).header es H.code seed)
  have boot:=(v.wide_signed_boot_at h width size extent stock v.radius π.symm order raw boxed.endFits).2.2.1
  have occurs : Event.attempt a ∈ es := by
    have eqn : es = H.prior ++ .attempt a :: tail := H.cut.events
    rw [eqn]
    simp
  have limit : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤h:=(Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans (dims).market)
  exact v.wide_elected_source h width r banks source table target owners π.symm initial a H.prior tail entry H.cut
    boot boxed.resident boxed.nativeStock.mounted_all boxed.endFits boxed.archives (dims).strip boxed.payload limit
    catRoom cols stages degree (boxed.boards a occurs).1 i (H.committed_at extent i hit)

private structure ElectedPacketShape where
  Index : Type
  code : Index → Prop
  terms : Index → Prop
  Source : Type

private abbrev electedPacketShape (i : Fin ((C).layout a).candidates) : ElectedPacketShape where
  Index := v.widePacketMenuIndex h a
  code atom := ((batch).packet.eval (snap x) (i.val:Word w)).val = v.widePacketNumber h a atom
  terms atom := ((batch).termCount.read (snap x) ((batch).packet.eval (snap x) (i.val:Word w))).val =
    v.widePacketTerms h a atom
  Source := v.ElectedSource h width π.symm marks ends co a i.val

private structure ElectedPacketData {T : Type} (index : T) (spec : ElectedPacketShape) where
  atom : spec.Index
  nativeCode : spec.code atom
  nativeTerms : spec.terms atom
  installed : spec.Source

/-- The finite menu atom is decoded before the trial writes its histogram. Its routes are taken from one accepted reference. -/
abbrev ElectedPacket (i : Fin ((C).layout a).candidates) : Type :=
  ElectedPacketData i (electedPacketShape H i)

namespace ElectedPacket
variable {H}
variable {i : Fin ((v.wideSignedChart h width (v.fixedTerminalStock (v.widePlacement h width) h width)).layout a).candidates}
  (packet : H.ElectedPacket i)

abbrev mk := @ElectedPacketData.mk _ i (electedPacketShape H i)
abbrev rec := @ElectedPacketData.rec _ i (electedPacketShape H i)
abbrev casesOn := @ElectedPacketData.casesOn _ i (electedPacketShape H i)
abbrev atom := ElectedPacketData.atom packet
abbrev nativeCode := ElectedPacketData.nativeCode packet
abbrev nativeTerms := ElectedPacketData.nativeTerms packet
abbrev installed := ElectedPacketData.installed packet
end ElectedPacket

include boxed extent catRoom cols stages degree in
def electedPacket (i : Fin ((C).layout a).candidates) (hit : (batch).selected (snap x) (i.val:Word w)) :
    H.ElectedPacket i := by
  let decoded:=v.funded_packet_word h width size extent π seed age budget small t i hit
  exact ⟨decoded.choose,decoded.choose_spec.1,decoded.choose_spec.2,
    H.electedSource boxed extent catRoom cols stages degree i hit⟩

namespace ElectedPacket
variable {H}
variable {i : Fin ((v.wideSignedChart h width (v.fixedTerminalStock (v.widePlacement h width) h width)).layout a).candidates} (u : H.ElectedPacket i)
    (rt : Fin (v.wideBallotParties h a))

def menu := u.installed.placed u.atom rt

omit [Nonempty (Fin k)] in
theorem atom_agrees {c' : (slots (.attempt a)).choice x}
    {other : v.FundedDate h width size π seed age budget small t c'} (v' : other.ElectedPacket i) :
    u.atom=v'.atom := (v.widePacketNumber_injective h a) (u.nativeCode.symm.trans v'.nativeCode)

omit [Nonempty (Fin k)] in
theorem arity : (u.menu rt).data.terms=((batch).termCount.read (snap x) ((batch).packet.eval (snap x) (i.val:Word w))).val :=
  (u.installed.terms u.atom rt).trans u.nativeTerms.symm

def route (pad : LinearAlgebra.SpectralBooks.ChordGraph.Chord (siteLast h D k+1)) :
    ChosenPackets.RowRouting (ChosenPackets.Row.packet (u.menu rt) (batch).copies)
      (CatalogueRows.installedRows π.symm ends (siteNumber h D k).toEmbedding pad) :=
  u.installed.routing u.atom rt (batch).copies pad

end ElectedPacket
end FundedDate

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
