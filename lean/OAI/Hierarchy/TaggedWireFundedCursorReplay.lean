import OAI.Hierarchy.TaggedWireFundedCursor
import OAI.Hierarchy.TaggedWirePastGoods

namespace OAI
/-! # The signed state on a partial cursor equals its original complete tape at that date -/

noncomputable section
set_option quotPrecheck false
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


variable (size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
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
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

open Filter CalendarTape
local notation "lo" j:arg => (A).first+j*(A).stride
local notation "slab" => v.slab (v.seed P h width) P width
local notation "curr" => v.wideCursorWidth h width size π seed age budget small

def cursorReplayHeight:=Classical.choose (eventually_atTop.1 v.wide_past_wireAt)

set_option maxHeartbeats 1800000 in
include extent in
theorem wide_cursor_replay {tail x} (t : WireTelescope.CalendarTape.Prefix slots es base tail x) (suffix : Path slots tail x)
    (late : v.cursorReplayHeight≤h) :
    let j := (es).length-tail.length
    let code:=encode slots es base (t.withSuffix suffix)
    let native:=origin code
    curr t=v.wireAt h width v.maxBits π.symm j (StockBound.state C native j) := by
  let j:=(es).length-tail.length
  let code:=encode slots es base (t.withSuffix suffix)
  let native:=origin code
  obtain ⟨past,split,agree⟩:=v.original_suffix_replay P h width r banks source table target owners
    (dims).words.addresses (dims).copies size input π auth extent heap
    (v.funded_page_mounted h width size extent π seed age budget small) t suffix
  change ReadBanks.Agree ((reader).hidden tail) x (run C past (Boot.booted V size ((L).header es code original))) at agree
  rw [←v.funded_boot_page h width size π seed age budget small code] at agree
  have len:=congrArg List.length split
  simp only [List.length_append] at len
  have last : j≤(es).length:=Nat.sub_le ..
  have idx : j=past.length:=by dsimp [j];omega
  have prior : StockBound.state C native j=run C past native:=by
    change run C ((es).take j) native=_
    rw [idx,split,List.take_left]
  have low : PrefixAgreement.Low (lo j) x (StockBound.state C native j):=by
    rw [prior]
    intro u hu
    apply agree u
    rintro ⟨e,on,part⟩
    obtain ⟨i,hi,hits⟩:=List.mem_iff_getElem.mp on
    have within : past.length+i<(es).length:=by omega
    have eqn : (es)[past.length+i]=e:=by
      simpa [split,List.getElem_append_right] using hits
    have atDate:=position_at v.mesh within
    rw [eqn] at atDate
    have first : lo j≤(A).base v.mesh e:=by
      unfold Arena.base
      rw [atDate,idx]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_add_right ..)) _
    let k' : Fin ((L).cells e):=⟨u-(L).base e,by have h:=part.1;have h':=part.2;omega⟩
    have pageStart:=Slab.page_lower slab s F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
      (P).catalogue banks source table target owners (v.original_selector_room P h width (dims).words.addresses)
      (v.original_copy_room P h width r banks source table target owners (dims).copies) e k'
    change (A).base v.mesh e ≤ (L).base e + k'.val at pageStart
    have pastEnd : (A).base v.mesh e ≤ u := by
      exact pageStart.trans_eq (Nat.add_sub_of_le part.1)
    exact (Nat.not_le_of_lt hu) (first.trans pastEnd)
  let tape:=v.wideFundedRaw h width v.maxBits ((L).header es code seed)
  exact Classical.choose_spec (eventually_atTop.1 v.wide_past_wireAt) h late width small budget
    size extent π.symm tape v.maxBits j last x low (v.past_goods_agreement h width j last x _ low)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
