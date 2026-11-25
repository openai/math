import OAI.Hierarchy.TaggedWireFundedDate
import OAI.Hierarchy.TaggedWireOriginalLedger
import OAI.Hierarchy.TaggedWireWideFeedOperator

namespace OAI
/-! # Exact named ledger at each reachable cut of the funded family -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
attribute [local irreducible] Nat.pow
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
private structure PresentedFeed (Gate : Type) (acts presented : Gate → Prop) where
  gate : Gate
  action : acts gate
  receipt : presented gate

private structure FeedCursorDate (Code : Type) (schedule : List Event) (step : Event)
    (cutAt : Code → List Event → Prop) (before after inputWidth outputWidth : Code → Fin schedule.length → Prop) where
  code : Code
  prior : List Event
  cut : cutAt code prior
  date : Fin schedule.length
  tag : schedule[date.val] = step
  ordinal : date.val = prior.length
  entry : before code date
  exitAt : after code date
  inputAt : inputWidth code date
  outputAt : outputWidth code date

private theorem FeedCursorDate.expose {Code : Type} {schedule : List Event} {step : Event}
    {cutAt : Code → List Event → Prop} {before after inputWidth outputWidth : Code → Fin schedule.length → Prop}
    (entry : FeedCursorDate Code schedule step cutAt before after inputWidth outputWidth)
    (seen : ∀ (_ : Code) (date : Fin schedule.length), schedule[date.val]=step → Prop)
    (ok : seen entry.code entry.date entry.tag) :
    ∃(code : Code) (past : List Event) (_cut : cutAt code past) (date : Fin schedule.length)
      (tag : schedule[date.val]=step), date.val=past.length ∧ before code date ∧ after code date ∧ seen code date tag :=
  ⟨entry.code,entry.prior,entry.cut,entry.date,entry.tag,entry.ordinal,entry.entry,entry.exitAt,ok⟩

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
local notation "mid" => v.wideSignedMidAt h width size stock M π order

local notation "funded" => v.wideFundedRaw h width v.maxBits seed
local notation "original" => v.wideSignedWords h width stock v.radius π.symm order funded
local notation "V" => v.catalystMarkets P h width
local notation "input" => fun _ : Equiv.Perm (Row h)=>original
local notation "dims" => v.wide_stock_sizes h width age budget small
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open LinearAlgebra.SpectralBooks ChordGraph
open CalendarTape
open scoped BigOperators

def wideCursorWidth {tail x} (_ : CalendarTape.Prefix slots es base tail x) :=
  v.wireAt h width v.maxBits π.symm ((es).length-tail.length) x

include extent in
theorem wide_cursor_head :
    exposedWidth π D k width (fuel v.mesh*width)=
      v.wideCursorWidth h width size π seed age budget small CalendarTape.Prefix.start := by
  simpa only [wideCursorWidth,Nat.sub_self] using
    (v.wire_origin h width size seed π extent age budget small).symm

local notation "curr" => v.wideCursorWidth h width size π seed age budget small


include extent in
private def cursorFeedDate {b : Boundary} {tail x} (t : CalendarTape.Prefix slots es base (.feed b::tail) x) :
    FeedCursorDate (Bits (CalendarTape.bits slots es)) es (.feed b)
      (fun key past => Calendar.Slot C (origin key) (.feed b) past tail x)
      (fun key date => StockBound.state C (origin key) date.val=x)
      (fun key date => StockBound.state C (origin key) (date.val+1)=after C (.feed b) x)
      (fun key date => v.wireAt h width v.maxBits π.symm date.val (StockBound.state C (origin key) date.val)=curr t)
      (fun key date => ∀ c : (slots (.feed b)).choice x, v.wireAt h width v.maxBits π.symm (date.val+1)
        (StockBound.state C (origin key) (date.val+1))=curr (t.advance c)) := by
  classical
  let above:=(v.wide_funded_cuts h width size extent π seed age budget small t).1
  let key:=Classical.choose above
  let past:=Classical.choose (Classical.choose_spec above)
  have cut : Calendar.Slot C (origin key) (.feed b) past tail x := Classical.choose_spec (Classical.choose_spec above)
  have eventList : es = past ++ .feed b :: tail := cut.events
  let entryTape:=origin key
  let lo : past.length<(es).length:=by rw [eventList];simp
  let date : Fin (es).length:=⟨past.length,lo⟩
  have tag : (es)[date.val]=.feed b:=by
    have head : ((es)[date.val]?)=some (.feed b):=by simp [date,eventList]
    simpa only [List.getElem?_eq_getElem date.isLt,Option.some.injEq] using head
  have pre : StockBound.state C entryTape date.val=x:=by
    change run C ((es).take past.length) entryTape=x
    rw [eventList,List.take_left]
    exact cut.entry
  have post : StockBound.state C entryTape (date.val+1)=after C (.feed b) x:=by
    have chartTag : (events (C).mesh)[date.val]'(show date.val < (events (C).mesh).length from date.isLt)=.feed b := tag
    exact (StockBound.state_succ C entryTape date.val date.isLt).trans (congrArg₂ (after C) chartTag pre)
  have counts:=congrArg List.length eventList
  simp only [List.length_append,List.length_cons] at counts
  have e0 : date.val=(es).length-(Event.feed b::tail).length:=by
    change past.length=(es).length-(tail.length+1)
    omega
  have e1 : date.val+1=(es).length-tail.length:=by
    change past.length+1=(es).length-tail.length
    omega
  have m0 : v.wireAt h width v.maxBits π.symm date.val (StockBound.state C entryTape date.val)=curr t:=by
    rw [pre,e0];rfl
  have m1 (c : (slots (.feed b)).choice x) :
      v.wireAt h width v.maxBits π.symm (date.val+1) (StockBound.state C entryTape (date.val+1))=
        curr (t.advance c):=by
    rw [post,e1];rfl
  exact ⟨key,past,cut,date,tag,rfl,pre,post,m0,m1⟩

local notation "cursorDate" t:arg => cursorFeedDate v h width size extent π seed age budget small t

private theorem feedPresentation_rebase {K : ℕ} {BaseField : Type} {U «V» U' V' : Widths K}
    (valid : ∀ {U «V» : Widths K}, SiteMatrix (State U) (State «V») BaseField → Prop)
    {gate : SiteMatrix (State U) (State «V») BaseField} (ok : valid gate)
    (left : U=U') (right : «V»=V') : valid (WireTelescope.rebase left right gate) := by
  subst U'
  subst V'
  exact ok

attribute [local irreducible] wire_feed_operator wireFeedPresentation cursorFeedDate

include extent in
private def presentedCursorFeed {b : Boundary} {tail x}
    (t : CalendarTape.Prefix slots es base (.feed b::tail) x) (late : v.feedOperatorHeight≤h) :
    let info:=cursorDate t
    let tape:=v.wideFundedRaw h width v.maxBits ((L).header es info.code seed)
    PresentedFeed (∀c : (slots (.feed b)).choice x, SiteMatrix (State (curr t)) (State (curr (t.advance c))) F)
      (fun op=>∀y,(raw F (curr t)).coeff y=∑c,SiteMatrix.act (op c) (raw F (curr (t.advance c))).coeff y)
      (fun op=>∀c,v.wireFeedPresentation (U:=curr t) («V»:=curr (t.advance c)) h width size extent π.symm tape
        late budget small v.maxBits info.date b info.tag (op c)) := by
  let info:=cursorDate t
  let tape:=v.wideFundedRaw h width v.maxBits ((L).header es info.code seed)
  let paid:=v.wire_feed_operator h width size extent π.symm tape late budget small v.maxBits info.date b info.tag
  refine ⟨fun c=>rebase info.inputAt (info.outputAt c) paid.1,?_,?_⟩
  · intro y
    change _=∑c : Unit,SiteMatrix.act (rebase info.inputAt (info.outputAt c) paid.1) (raw F (curr (t.advance c))).coeff y
    simpa only [Fintype.sum_unique] using rebase_action info.inputAt (info.outputAt ()) paid.1 paid.2 y

  · intro c
    let sourceWidth:=v.wireAt h width v.maxBits π.symm info.date.val (StockBound.state C (origin info.code) info.date.val)
    let targetWidth:=v.wireAt h width v.maxBits π.symm (info.date.val+1) (StockBound.state C (origin info.code) (info.date.val+1))
    let valid := fun {U «V» : Widths (siteLast h D k+1)} (op : SiteMatrix (State U) (State «V») F) =>
      v.wireFeedPresentation (U:=U) («V»:=«V») h width size extent π.symm tape late budget small v.maxBits info.date b info.tag op
    have receipt : @valid sourceWidth targetWidth paid.1 :=
      v.wire_feed_presents h width size extent π.symm tape late budget small v.maxBits info.date b info.tag
    exact @feedPresentation_rebase (siteLast h D k+1) F sourceWidth targetWidth (curr t) (curr (t.advance c)) @valid paid.1 receipt info.inputAt (info.outputAt c)

attribute [local irreducible] presentedCursorFeed

include extent in
/-- The genuine feed transfer on the original packet-free chronological slot.
Even a state with arbitrary later private bits has an exact funded native
realization, so the cap matrix can be used without assuming future admission. -/
def wide_cursor_feed {b : Boundary} {tail x}
    (t : CalendarTape.Prefix slots es base (.feed b::tail) x) (late : v.feedOperatorHeight≤h) :
    {op : ∀c : (slots (.feed b)).choice x,
      SiteMatrix (State (curr t)) (State (curr (t.advance c))) F //
      ∀y,(raw F (curr t)).coeff y=∑c,SiteMatrix.act (op c) (raw F (curr (t.advance c))).coeff y} := by
  let paid:=presentedCursorFeed v h width size extent π seed age budget small t late
  exact ⟨paid.gate,paid.action⟩

set_option maxHeartbeats 8000000 in
include extent in
theorem cursor_feed_presents {b : Boundary} {tail x}
    (t : CalendarTape.Prefix slots es base (.feed b::tail) x) (late : v.feedOperatorHeight≤h) :
    ∃(key : Bits (CalendarTape.bits slots es)) (past : List Event)
      (_cut : Calendar.Slot C (origin key) (.feed b) past tail x) (date : Fin (es).length)
      (tag : (es)[date.val]=.feed b),
      date.val=past.length ∧ StockBound.state C (origin key) date.val=x ∧
      StockBound.state C (origin key) (date.val+1)=after C (.feed b) x ∧
      ∀c : (slots (.feed b)).choice x, v.wireFeedPresentation (U:=curr t) («V»:=curr (t.advance c)) h width size extent π.symm
        (v.wideFundedRaw h width v.maxBits ((L).header es key seed)) late budget small v.maxBits date b tag
        ((v.wide_cursor_feed h width size extent π seed age budget small t late).1 c) := by
  let info:=cursorDate t
  let paid:=presentedCursorFeed v h width size extent π seed age budget small t late
  exact FeedCursorDate.expose info (fun key date tag => ∀c : (slots (.feed b)).choice x,
    v.wireFeedPresentation (U:=curr t) («V»:=curr (t.advance c)) h width size extent π.symm
      (v.wideFundedRaw h width v.maxBits ((L).header es key seed)) late budget small v.maxBits date b tag (paid.gate c)) paid.receipt

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
