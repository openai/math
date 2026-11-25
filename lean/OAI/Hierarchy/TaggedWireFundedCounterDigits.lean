import OAI.Hierarchy.TaggedWireFundedBranchWord
import OAI.Hierarchy.TaggedWireFundedBallots
import OAI.Hierarchy.TaggedWireMeasuredHistogram
import OAI.Hierarchy.TaggedWireFundedEarnedAgreement

namespace OAI
/-! # Native ballot digits and recommendation at the priced stage of each funded history -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open CalendarTape StockCommit ProtocolRAM.PurchaseStage ThreeFlat.Diagonal.MotifOuterTerms
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

local notation "slab" => v.slab (v.seed P h width) P width
local notation "EF" => Slab.effects slab s F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
  (P).catalogue banks source table target owners
local notation "pageRoom" => v.original_selector_room P h width (dims).words.addresses
local notation "copyRoom" => v.original_copy_room P h width r banks source table target owners (dims).copies
local notation "floorE" e => (A).base v.mesh e
local notation "ceilE" e => (A).base v.mesh e+(A).stride
local notation "top" => (A).endAddress v.mesh


namespace FundedDate
variable {v h width size π seed age budget small} {a : Attempt} {tail : List Event}
    {x : Memory (Native.wordBits h (2^v.W) Native.copies)}
    {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (.attempt a::tail) x} {c : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
    (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (tall : v.ballotHeight≤h) (floor : v.widthFloor≤width)
local notation "entry" => run C H.prior (origin H.code)
local notation "b" => PurchaseStage.enabledBatch ((C).layout a) (repair C a)
local notation "snap" y => HistogramShelf.snapshot C a y
local notation "paid" => v.stage P h width r banks source table target owners a entry
local notation "format" => (reader).format
local notation "signal" i => (b).selected (snap x) ((i).val:Word w)
local notation "alphEq" => (v.catalogue_words (v.seed P h width) width).1
local notation "I" => Fin ((C).layout a).candidates

/-- The original tile IDs and stock addresses at the repair input agree with a
different accepted continuation's checkout, throughout the common old prefix. -/
theorem priced_before {other : (slots (.attempt a)).choice x}
    (ref : v.FundedDate h width size π seed age budget small t other) :
    PrefixAgreement.Low ((A).base v.mesh (.attempt a)) paid
      (checkedOut C ((A).endAddress v.mesh) (origin ref.code)) := by
  let fmt:=v.nativeFormats P h width a
  let stamp:=v.stamp P h width r banks source table target owners a
  let posted:=postOutput ((C).layout a) (repair C a) (prepared C a entry)
  have label : (A).base v.mesh (.attempt a) ≤ stamp.out:=v.stock_label P h width a
  have beforeSeed : stamp.out ≤ fmt.pricedArea.start:=Nat.le_add_right ..
  intro addr low
  have before : posted addr=entry addr := postOutput_prior C a entry addr H.cut.currentReady
    ((v.event_prefix P h width r banks source table target owners (.attempt a) addr low).1)
  have prior : paid addr=posted addr :=
    StockCommit.stage_frame fmt.pricedArea fmt.stockSource stamp posted addr (low.trans_le label) beforeSeed
  exact prior.trans (before.trans ((H.before addr low).symm.trans (ref.checkout_input addr low).symm))

include extent tall floor in
theorem priced_snapshot (i : I) (positive : 0<v.menu.alphabet) :
    (b).packet.eval paid (i.val:Word w)=(b).packet.eval (snap entry) (i.val:Word w) ∧
      (b).termCount.read paid ((b).packet.eval paid (i.val:Word w))=
        (b).termCount.read (snap entry) ((b).packet.eval (snap entry) (i.val:Word w)) ∧
      ∀j:Fin v.menu.alphabet,((b).field (j.cast (alphEq).symm)).eval paid (i.val:Word w)=((b).field (j.cast (alphEq).symm)).eval (snap entry) (i.val:Word w) := by
  let acceptedRun:=H.readbackRun extent tall floor
  have live : Event.attempt a∈events v.mesh := by
    have eqn : events v.mesh = H.prior ++ .attempt a :: tail := H.cut.events
    rw [eqn]
    simp
  have board:=(acceptedRun.boards a live).1
  have bound:=v.ballot_before P h width r banks source table target owners a
  have native := priced_histogram_inputs ((C).layout a) (repair C a) (v.nativeFormats P h width a).pricedArea
    (v.nativeFormats P h width a).stockSource (v.stamp P h width r banks source table target owners a)
    (prepared C a entry) H.cut.currentReady.2.2.2.2.2.2.1 H.cut.currentReady.2.2.2.2.2.2.2.1
    bound (bound.trans (Nat.le_succ _)) board.window.label (positive.trans_eq (alphEq).symm) (i.val:Word w)
  exact ⟨native.1, native.2.1, fun j => native.2.2 (j.cast (alphEq).symm)⟩

include extent tall floor in
/-- Each digit actually committed in the priced ballot is the corresponding component
of this history's own histogram submitted at the original selector page. -/
theorem priced_digit (i : I) (j : Fin ((format).letters a x i)) :
    let fieldIndex:=j.castLE ((format).width a x i)
    (((b).field fieldIndex).eval paid (i.val:Word w)).val=((c i).val j).val := by
  intro fieldIndex
  have positive : 0<v.menu.alphabet := (Nat.zero_le j.val).trans_lt (j.isLt.trans_le (((format).width a x i).trans_eq alphEq))
  have atEntry : ((b).field fieldIndex).eval (snap entry) (i.val:Word w)=
      counterRows ((format).letters a x) ((format).copies a x) c ((format).count a x) i fieldIndex :=
    (format).field_on_branch a x entry c i fieldIndex H.cut.currentReady
      (v.ballot_shelf_safe P h width r banks source table target owners a
        (dims).words.addresses (dims).copies) H.ballot_word
  exact (congrArg Fin.val (((H.priced_snapshot extent tall floor i positive).2.2 (fieldIndex.cast alphEq)).trans atEntry)).trans
    (counter_of_active ((format).letters a x) ((format).copies a x) c ((format).width a x) ((format).count a x) i j)

include extent tall floor in
/-- Numerical menu evidence for the fixed elected atom in this row, including its exact alphabet. -/
theorem priced_election {other : (slots (.attempt a)).choice x}
    {ref : v.FundedDate h width size π seed age budget small t other}
    (i : I) (u : ref.ElectedPacket i) (positive : 0<v.menu.alphabet) :
    ((b).packet.eval paid (i.val:Word w)).val=v.widePacketNumber h a u.atom ∧
      ((b).termCount.read paid ((b).packet.eval paid (i.val:Word w))).val=v.widePacketTerms h a u.atom := by
  have hs:=H.priced_snapshot extent tall floor i positive
  have pre:=H.ballot extent i
  exact ⟨(congrArg Fin.val (hs.1.trans pre.1.symm)).trans u.nativeCode,
    (congrArg Fin.val (hs.2.1.trans pre.2.1.symm)).trans u.nativeTerms⟩


include extent tall floor in
/-- Compare the native row directly with the occurrence histogram after the
dependent term/count casts used by the original elected tender. -/
theorem tender_digits (i : I) {n mass : ℕ}
    (letters : (format).letters a x i=n) (count : (format).copies a x i=mass)
    (j : Fin n) :
    let bound : n≤v.menu.alphabet:=letters ▸ ((format).width a x i).trans_eq alphEq
    let hist:=cast (congrArg₂ (fun n t=>Histogram (Fin n) t) letters count) (c i)
    (((b).field (j.castLE (bound.trans_eq (alphEq).symm))).eval paid (i.val:Word w)).val=(hist.val j).val := by
  intro bound hist
  change _=((cast (congrArg₂ (fun n t=>Histogram (Fin n) t) letters count) (c i)).val j).val
  rw [cast_counter letters count]
  exact H.priced_digit extent tall floor i (j.cast letters.symm)

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
