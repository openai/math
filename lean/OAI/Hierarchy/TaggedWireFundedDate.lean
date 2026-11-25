import OAI.Hierarchy.TaggedWireFundedContinuation
import OAI.Hierarchy.TaggedWireFundedElection

namespace OAI
/-! # Physical admissible date for each summand of an unfinished signed history -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
private theorem dateRangeEffects {w q d : ℕ} {C : Chart w q d}
    (reader : CalendarTape.CounterROM C) (effect : CalendarTape.CounterROM.Effects C)
    (e : Event) (tail : List Event) (x real : Memory w) (c : (reader.format.slot e).choice x)
    (lo top : ℕ) (loEnd : lo ≤ effect.endAt e) (endTop : effect.endAt e ≤ top)
    (earlier : ∀u, reader.format.windows.inside e u → lo ≤ u)
    (later : ∀ f ∈ tail, ∀u, reader.format.windows.inside f u → effect.endAt e ≤ u)
    (outer : ∀ f ∈ e :: tail, ∀u, reader.format.windows.inside f u → u < top)
    (readyX : ready C e (reader.patch e x c)) (readyReal : ready C e real)
    (same : ReadBanks.Agree (reader.hidden tail) (reader.patch e x c) real) :
    Below lo x real ∧ Below (effect.endAt e) (reader.patch e x c) real ∧
    Below (effect.endAt e) ((reader.format.slot e).next x c) (after C e real) ∧
    (∀u,top≤u → x u=real u ∧ ((reader.format.slot e).next x c) u=after C e real u) ∧
    ReadBanks.Agree (reader.hidden tail) ((reader.format.slot e).next x c) (after C e real) := by
  have current : Below (effect.endAt e) (reader.patch e x c) real := by
    intro u hu
    exact same u (fun ⟨f,hf,hit⟩ => (Nat.not_le_of_lt hu) (later f hf u hit))
  have nextRead := effect.read e _ real readyX readyReal current
  have before : Below lo x real := by
    intro u hu
    have off : ¬reader.format.windows.inside e u := fun hit => (Nat.not_le_of_lt hu) (earlier u hit)
    exact (reader.format.windows.install_off e _ x u off).symm.trans (current u (hu.trans_le loEnd))
  rw [reader.commit_patch]
  refine ⟨before,current,nextRead,?_,?_⟩
  · intro u hu
    have off (f) (hf : f ∈ e :: tail) : ¬reader.format.windows.inside f u :=
      fun hit => (Nat.not_lt_of_ge hu) (outer f hf u hit)
    have eqn := same u (fun ⟨f,hf,hit⟩ => off f (List.mem_cons_of_mem _ hf) hit)
    refine ⟨(reader.format.windows.install_off e _ x u (off e (List.mem_cons_self ..))).symm.trans eqn,?_⟩
    exact (effect.frame e _ readyX u (endTop.trans hu)).trans (eqn.trans (effect.frame e real readyReal u (endTop.trans hu)).symm)
  · intro u outside
    by_cases low : u < effect.endAt e
    · exact nextRead u low
    · exact (effect.frame e _ readyX u (Nat.le_of_not_gt low)).trans
        ((same u outside).trans (effect.frame e real readyReal u (Nat.le_of_not_gt low)).symm)

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
local notation "floorE" => (A).base v.mesh
local notation "ceilE" => fun e : Event => (A).base v.mesh e + (A).stride
local notation "top" => (A).endAddress v.mesh

private theorem laterDates {α : Type} {R : α → α → Prop} {all prior tail : List α} {head : α}
    (ordered : all.Pairwise R) (atHead : all = prior ++ head :: tail) : ∀ f ∈ tail, R head f :=
  (List.pairwise_cons.mp (List.pairwise_append.mp (atHead ▸ ordered)).2.1).1

private theorem lower_of_inside {floor loAddr cells address : ℕ} (lo : loAddr ≤ address)
    (hi : address < loAddr + cells) (atCell : ∀ i : Fin cells, floor ≤ loAddr + i.val) : floor ≤ address := by
  have below := atCell ⟨address - loAddr, by omega⟩
  exact below.trans_eq (Nat.add_sub_of_le lo)

private structure FundingDateShape where
  Code : Type
  valid : Code → Prop
  cut : Code → List Event → Prop
  before : Code → List Event → Prop
  current : Code → List Event → Prop
  next : Code → List Event → Prop
  upper : Code → List Event → Prop
  currentOff : Code → List Event → Prop
  nextOff : Code → List Event → Prop

private def fundingDateShape (e : Event) (tail : List Event) (x : Memory w) (c : (slots e).choice x) :
    FundingDateShape where
  Code := Bits (CalendarTape.bits slots es)
  valid code := admissible C es (origin code)
  cut code prior := Calendar.Slot C (origin code) e prior tail (run C prior (origin code))
  before code prior := Below (floorE e) x (run C prior (origin code))
  current code prior := Below (ceilE e) ((reader).patch e x c) (run C prior (origin code))
  next code prior := Below (ceilE e) ((slots e).next x c) (after C e (run C prior (origin code)))
  upper code prior := ∀u,top≤u→x u=run C prior (origin code) u ∧
    ((slots e).next x c) u=after C e (run C prior (origin code)) u
  currentOff code prior := ReadBanks.Agree ((reader).hidden tail) ((reader).patch e x c) (run C prior (origin code))
  nextOff code prior := ReadBanks.Agree ((reader).hidden tail) ((slots e).next x c) (after C e (run C prior (origin code)))

local notation "specAt" => fundingDateShape v h width size π seed age budget small

private structure FundingDateEvidence {T : Type} (index : T) (spec : FundingDateShape) where
  code : spec.Code
  prior : List Event
  valid : spec.valid code
  cut : spec.cut code prior
  before : spec.before code prior
  current : spec.current code prior
  next : spec.next code prior
  upper : spec.upper code prior
  currentOff : spec.currentOff code prior
  nextOff : spec.nextOff code prior

attribute [reducible] fundingDateShape

/-- A real accepted occurrence at the same event on the same tag and immutable
ROM. The states agree on the whole event slab, and all words above the
calendar are identical, even when the original continuation was rejected. -/
abbrev FundedDate {e : Event} {tail : List Event} {x : Memory w}
    (t : CalendarTape.Prefix slots es base (e::tail) x) (c : (slots e).choice x) : Type :=
  FundingDateEvidence t (specAt e tail x c)

namespace FundedDate
variable {v h width size π seed age budget small}
variable {e : Event} {tail : List Event} {x : Memory (Native.wordBits h (2^v.W) Native.copies)}
    {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh)
      (v.wideOrigin h width size seed π) (e::tail) x} {c : ((v.wideSelector h width age budget small).format.slot e).choice x}
    (witness : v.FundedDate h width size π seed age budget small t c)
abbrev mk := @FundingDateEvidence.mk _ t (specAt e tail x c)
abbrev rec := @FundingDateEvidence.rec _ t (specAt e tail x c)
abbrev casesOn := @FundingDateEvidence.casesOn _ t (specAt e tail x c)
abbrev code := FundingDateEvidence.code witness
abbrev prior := FundingDateEvidence.prior witness
abbrev valid := FundingDateEvidence.valid witness
abbrev cut := FundingDateEvidence.cut witness
abbrev before := FundingDateEvidence.before witness
abbrev current := FundingDateEvidence.current witness
abbrev next := FundingDateEvidence.next witness
abbrev upper := FundingDateEvidence.upper witness
abbrev currentOff := FundingDateEvidence.currentOff witness
abbrev nextOff := FundingDateEvidence.nextOff witness
end FundedDate

include extent in
def wide_funded_date_with {e : Event} {tail : List Event} {x : Memory w}
    (t : CalendarTape.Prefix slots es base (e::tail) x) (c : (slots e).choice x)
    (future : CalendarTape.Path slots tail ((slots e).next x c)) :
    v.FundedDate h width size π seed age budget small t c := by
  classical
  let code:=CalendarTape.encode slots es base (t.withSuffix ⟨c,future⟩)
  have trace:=v.wide_completed_cut h width size extent π seed age budget small t c future
  let prior:=Classical.choose trace.2
  let real:=run C prior (origin code)
  have atDate:=Classical.choose_spec trace.2
  have cut : Calendar.Slot C (origin code) e prior tail real:=atDate.1
  have same : ReadBanks.Agree ((reader).hidden tail) ((reader).patch e x c) real:=atDate.2
  let upperPage:=Slab.page_end slab s F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
    (P).catalogue banks source table target owners pageRoom copyRoom
  let lowerPage:=Slab.page_lower slab s F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
    (P).catalogue banks source table target owners pageRoom copyRoom
  have dated:=Slab.dates_separate slab s F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
    (P).catalogue banks source table target owners pageRoom copyRoom
  have eventOrder : es = prior ++ e :: tail := cut.events
  have dates := laterDates dated eventOrder
  have honest:=(v.wide_funded_cuts h width size extent π seed age budget small t).2 c
  have localCut := honest.choose_spec.choose_spec
  have insideLow (f : Event) (u : ℕ) (hit : (L).inside f u) : floorE f≤u :=
    lower_of_inside hit.1 hit.2 (lowerPage f)
  have present : e ∈ es := by rw [eventOrder]; simp
  have outside (f : Event) (future : f ∈ e :: tail) (u : ℕ) (hit : (L).inside f u) : u < top := by
    have atDate : f ∈ es := by rw [eventOrder]; exact List.mem_append_right prior future
    exact hit.2.trans_le ((upperPage f).trans ((A).within v.mesh f atDate))
  have memory := dateRangeEffects reader EF e tail x real c (floorE e) top
    (Nat.le_add_right ..) ((A).within v.mesh e present) (insideLow e) dates outside
    localCut.currentReady cut.currentReady same
  exact ⟨code,prior,trace.1,cut,memory.1,memory.2.1,memory.2.2.1,
    memory.2.2.2.1,same,memory.2.2.2.2⟩

include extent in
def wide_funded_date {e : Event} {tail : List Event} {x : Memory w}
    (t : CalendarTape.Prefix slots es base (e::tail) x) (c : (slots e).choice x) :
    v.FundedDate h width size π seed age budget small t c :=
  v.wide_funded_date_with h width size extent π seed age budget small t c
    (v.wide_funded_continuation h width size extent π seed age budget small (t.advance c)).some

theorem wide_funded_date_code {e tail x} (t : CalendarTape.Prefix slots es base (e::tail) x)
    (c : (slots e).choice x) (future : CalendarTape.Path slots tail ((slots e).next x c)) :
    (v.wide_funded_date_with h width size extent π seed age budget small t c future).code=
      CalendarTape.encode slots es base (t.withSuffix ⟨c,future⟩) := rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
