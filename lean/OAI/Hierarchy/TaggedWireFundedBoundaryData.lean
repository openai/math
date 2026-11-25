import OAI.Hierarchy.TaggedWireFundedCursorReplay
import OAI.Hierarchy.TaggedWireFundedBallots

namespace OAI
/-! # Boundary and dated component readings on each genuine completed original tape -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
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

open Filter CalendarTape

namespace FundedDate
variable {v h width size π seed age budget small} {e : Event} {tail x}
    {t : WireTelescope.CalendarTape.Prefix slots es base (e::tail) x} {c : (slots e).choice x}
    (H : v.FundedDate h width size π seed age budget small t c)
local notation "pr" => H.prior.length
local notation "native" => origin (H.code)
local notation "tape" => v.wideFundedRaw h width v.maxBits ((L).header es H.code seed)
local notation "past" => run C H.prior native
local notation "post" => after C e past
local notation "curr" => v.wideCursorWidth h width size π seed age budget small
local notation "lo" j => (A).first+j*(A).stride

private theorem tape_eq : es = H.prior ++ e :: tail := H.cut.events

def index : Fin (es).length :=
  ⟨pr, (congrArg List.length H.tape_eq) ▸ (by simp)⟩

theorem index_event : (es).get H.index=e:=by
  have onDate (all prior : List Event) (date : Event) (rest : List Event)
      (split : all = prior ++ date :: rest) (bound : prior.length < all.length) :
      all[prior.length] = date := by
    subst all
    simp
  exact onDate es H.prior e tail H.tape_eq H.index.isLt

theorem clock : (es).length-(e::tail).length=pr ∧ (es).length-tail.length=pr+1:=by
  have total:=congrArg List.length H.tape_eq
  simp only [List.length_append,List.length_cons] at total ⊢
  omega

theorem prior_state : StockBound.state C native pr=past:=by
  change run C ((es).take pr) native=_
  have take_eq := congrArg (List.take pr) H.tape_eq
  exact congrArg (fun l => run C l native) (take_eq.trans List.take_left)

theorem next_state : StockBound.state C native (pr+1)=post:=by
  rw [StockBound.state_succ C native pr H.index.isLt,H.prior_state]
  exact congrArg (fun ev=>after C ev past) H.index_event

theorem before_low : PrefixAgreement.Low (lo pr) x past:=by
  have ord : position v.mesh e = pr := H.cut.ordinal
  rw [← ord]
  exact H.before

theorem next_low : PrefixAgreement.Low (lo (pr+1)) ((slots e).next x c) post:=by
  have ord : position v.mesh e = pr := H.cut.ordinal
  rw [← ord]
  intro addr below
  apply H.next addr
  simpa only [Arena.base,Nat.succ_mul,Nat.add_assoc] using below

theorem before_goods : v.wireGoodsAt h width pr x=v.wireGoodsAt h width pr past:=
  v.past_goods_agreement h width pr H.index.isLt.le x past H.before_low

theorem next_goods : v.wireGoodsAt h width (pr+1) ((slots e).next x c)=v.wireGoodsAt h width (pr+1) post:=
  v.past_goods_agreement h width (pr+1) H.index.isLt _ post H.next_low

theorem before_used : v.wireUsedAt h width pr x=v.wireUsedAt h width pr past:=by
  funext a
  exact v.past_reserve_agreement h width _ _ (dims).words.addresses pr H.before_low a

theorem next_used : v.wireUsedAt h width (pr+1) ((slots e).next x c)=v.wireUsedAt h width (pr+1) post:=by
  funext a
  exact v.past_reserve_agreement h width _ _ (dims).words.addresses (pr+1) H.next_low a

/-- The actual indexed incoming graph, including the endpoints of every positively
weighted purchased row, equals the graph of this realized prefix on its original tape. -/
theorem before_graph (extent : (A).endAddress v.mesh≤ size) (tall : v.cursorReplayHeight≤h) :
    curr t=v.wireAt h width v.maxBits π.symm pr (StockBound.state C native pr):=by
  change v.wireAt h width v.maxBits π.symm ((es).length-(e::tail).length) _=_
  rw [H.clock.1]
  apply Classical.choose_spec (eventually_atTop.1 v.wide_past_wireAt) h tall width small budget size extent π.symm tape
    v.maxBits pr H.index.isLt.le
  · exact H.prior_state.symm ▸ H.before_low
  · exact H.prior_state.symm ▸ H.before_goods

theorem next_graph (extent : (A).endAddress v.mesh≤ size) (tall : v.cursorReplayHeight≤h) :
    curr (t.advance c)=v.wireAt h width v.maxBits π.symm (pr+1) post:=by
  change v.wireAt h width v.maxBits π.symm ((es).length-tail.length) _=_
  rw [H.clock.2,←H.next_state]
  apply Classical.choose_spec (eventually_atTop.1 v.wide_past_wireAt) h tall width small budget size extent π.symm tape
    v.maxBits (pr+1) H.index.isLt
  · exact H.next_state.symm ▸ H.next_low
  · exact H.next_state.symm ▸ H.next_goods

theorem raw_past (extent : (A).endAddress v.mesh≤ size) (tall : v.feedPrefixHeight≤h)
    (causal : Classical.choose (eventually_atTop.1 v.wide_past_agreement)≤h) :
    v.wirePaidAt h width v.maxBits pr x=v.wirePaidAt h width v.maxBits pr past:=by
  let checked:=v.wideSignedCheckoutAt h width size stock v.radius π.symm order tape
  have mounted:=(v.wide_stock_at h width size extent v.radius π.symm tape age budget small).mounted_all
  have old:=v.wide_prestate_low h width size π.symm tape v.radius pr H.index.isLt.le mounted
  have priorState := H.prior_state
  unfold wideOrigin at priorState
  rw [priorState] at old
  have low : PrefixAgreement.Low (lo pr) checked x:=fun u hu=>((H.before_low u hu).trans (old u hu)).symm
  have right:=Classical.choose_spec (eventually_atTop.1 v.wide_past_agreement) h causal width small budget size extent
    π.symm tape v.maxBits pr x low
  have left:=(Classical.choose_spec (eventually_atTop.1 v.wide_wire_paid) h tall width small budget size extent
    π.symm tape v.maxBits).1 pr H.index.isLt.le
  rw [priorState] at left
  funext e
  exact (right e).symm.trans (left e).symm

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
