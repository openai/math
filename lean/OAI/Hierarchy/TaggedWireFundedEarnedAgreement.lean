import OAI.Hierarchy.TaggedWireFundedDate
import OAI.Hierarchy.ProbeFixedEarnedCross

namespace OAI
/-! # Original placement words agree in different accepted continuations -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing

/-- The last verdict and every transition from this chronological slot
onward preserve the strict prefix preceding its own slab. -/
theorem Slot.checkout_before {w q d : ℕ} {C : Chart w q d} {initial entry : Memory w}
    {e : Event} {prior tail : List Event} (cut : Slot C initial e prior tail entry)
    (A : Arena) (frame : ∀f x, x<A.base C.mesh f → protected C x f) :
    PrefixAgreement.Low (A.base C.mesh e) (checkedOut C (A.endAddress C.mesh) initial) entry := by
  intro x hx
  have live : e∈Calendar.events C.mesh:=by rw [cut.events];simp
  have top : x<A.endAddress C.mesh :=
    (hx.trans_le (Nat.le_add_right ..)).trans_le (A.within C.mesh e live)
  rw [checkedOut,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl top)]
  rw [cut.word x (fun later membership=>frame later x
    ((hx.trans_le (Nat.le_add_right ..)).trans_le (A.apart C.mesh (cut.later later membership))))]
  exact after_frame C e entry x cut.currentReady (frame e x hx)

namespace FixedProtocolFormat
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A))
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "owners" => sinkBank (v.catalystStaticStart P h width) cnt r (P).catalogue.rows
local notation "C" => v.wideSignedChart h width stock
local notation "top" => (A).endAddress v.mesh
local notation "es" => events v.mesh

variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (seed : Boot.Tape h (2^v.W))
  (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "slots" => (reader).format.slot
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b => v.wideOrigin h width size ((reader).format.windows.header es b seed) π
local notation "checkout" => fun code => checkedOut C top (origin code)

namespace FundedDate
variable {v h width size π seed age budget small} {e : Event} {rest : List Event} {x : Memory (Native.wordBits h (2^v.W) Native.copies)}
  {t : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh) (v.wideOrigin h width size seed π) (e::rest) x} {c c' : ((v.wideSelector h width age budget small).format.slot e).choice x}
  (H : v.FundedDate h width size π seed age budget small t c)

theorem checkout_input : PrefixAgreement.Low ((A).base v.mesh e) (checkout H.code) x := by
  have saved:=H.cut.checkout_before A (fun f z hz=>
    (v.event_prefix P h width r (TerminalLayout.settlement page stock) (TerminalLayout.source page)
      (TerminalLayout.table page) (TerminalLayout.destination page) owners f z hz).1)
  exact fun z hz=>(saved z hz).trans (H.before z hz).symm

theorem checkout_agree (H' : v.FundedDate h width size π seed age budget small t c') :
    PrefixAgreement.Low ((A).base v.mesh e) (checkout H.code) (checkout H'.code) :=
  fun z hz=>(H.checkout_input z hz).trans (H'.checkout_input z hz).symm

variable {a : Attempt} {path : CalendarTape.Prefix (v.wideSelector h width age budget small).format.slot (events v.mesh) (v.wideOrigin h width size seed π) (.attempt a::rest) x}
    {hist hist' : ((v.wideSelector h width age budget small).format.slot (.attempt a)).choice x}

theorem earned_reads (ref : v.FundedDate h width size π seed age budget small path hist)
    (alt : v.FundedDate h width size π seed age budget small path hist')
    (room : top<2^w) : v.EarnedReads h width a (checkout ref.code) (checkout alt.code) := by
  have calendarOrder : events v.mesh = ref.prior ++ .attempt a :: rest := ref.cut.events
  have member : Event.attempt a ∈ events v.mesh := by rw [calendarOrder]; simp
  exact v.wide_earned_words h width a (((Nat.le_add_right ..).trans
    ((A).within v.mesh (.attempt a) member)).trans_lt room) (ref.checkout_agree alt)

end FundedDate
end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
