import OAI.Hierarchy.TaggedWireOriginalExecution
import OAI.Hierarchy.TaggedWideHostAdmission
import OAI.Hierarchy.ProbeFixedFundedHeader
import OAI.Hierarchy.ProbeFixedReadbackProducer

namespace OAI
/-! # The physical terminal store for each original funded path -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart StripDirectory CatalogueRows ColumnWires BoughtSockets
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
local notation "origin" b:arg => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot
local notation "auth" => v.wide_signed_words_authentic h width stock v.radius π.symm order funded
local notation "heap" => (v.wideGeometryPrefix h width).2.1

theorem funded_boot_page (raw : Bits (CalendarTape.bits slots es)) :
    origin raw=Boot.booted V size ((L).header es raw original) := by
  unfold wideOrigin wideSignedMidAt
  rw [v.wide_funded_raw_header h width age budget small v.maxBits raw seed]
  apply congrArg (Boot.booted V size)
  exact v.wide_signed_header h width stock v.radius π.symm order r banks source table target owners
      (dims).words.addresses (dims).copies raw funded

local notation "pageEq" => v.funded_boot_page h width size π seed age budget small

include extent in
theorem funded_page_mounted (raw : Bits (CalendarTape.bits slots es)) :
    Calendar.mounted C es (Boot.booted V size ((L).header es raw original)) := by
  rw [←pageEq raw]
  exact (v.wide_stock_at h width size extent v.radius π.symm
    (v.wideFundedRaw h width v.maxBits ((L).header es raw seed)) age budget small).mounted_all

local notation "mountedAll" => v.funded_page_mounted h width size extent π seed age budget small

include extent in
theorem wide_funded_execution (j : CalendarTape.Path slots es base) :
    CalendarTape.terminal slots es base j=run C es (origin (CalendarTape.encode slots es base j)) := by
  rw [pageEq]
  exact v.original_execution P h width r banks source table target owners (dims).words.addresses (dims).copies
    size input π auth extent heap mountedAll j

include extent in
/-- On each side of the paid election, a real execution starts with the
same tag, public ROM and funded inventories and reads an original tape. -/
theorem wide_funded_cuts {e : Event} {tail : List Event} {x : Memory w}
    (t : CalendarTape.Prefix slots es base (e::tail) x) :
    (∃b : Bits (CalendarTape.bits slots es),∃prior,Calendar.Slot C (origin b) e prior tail x) ∧
    ∀c : (slots e).choice x,∃b : Bits (CalendarTape.bits slots es),∃prior,
      Calendar.Slot C (origin b) e prior tail ((reader).patch e x c) := by
  constructor
  · let T:=v.visited P h width r banks source table target owners (dims).words.addresses (dims).copies
      size input π auth extent heap mountedAll t
    refine ⟨T.bits,T.prior,?_⟩
    rw [pageEq T.bits]
    exact v.visited_slot P h width r banks source table target owners (dims).words.addresses (dims).copies
      size input π auth extent heap mountedAll t
  · intro c
    obtain ⟨b,prior,cut⟩:=v.visited_choice P h width r banks source table target owners
      (dims).words.addresses (dims).copies size input π auth extent heap mountedAll t c
    exact ⟨b,prior,(pageEq b).symm ▸ cut⟩

include extent in
theorem wide_completed_cut {e tail x} (t : CalendarTape.Prefix slots es base (e::tail) x)
    (c : (slots e).choice x) (next : CalendarTape.Path slots tail ((slots e).next x c)) :
    let full:=t.withSuffix ⟨c,next⟩
    let code:=CalendarTape.encode slots es base full
    let originalMem:=origin code
    admissible C es originalMem ∧
      ∃prior,Calendar.Slot C originalMem e prior tail (run C prior originalMem) ∧
        ReadBanks.Agree ((reader).hidden tail) ((reader).patch e x c) (run C prior originalMem) := by
  let j:=t.withSuffix ⟨c,next⟩
  let code:=CalendarTape.encode slots es base j
  let selected:=v.wideFundedRaw h width v.maxBits ((L).header es code seed)
  constructor
  · exact (v.wide_verdict h width size extent v.radius π.symm selected age budget small).1
      (v.wide_funded_path h width age budget small v.maxBits size extent v.radius π.symm seed j)
  · rw [pageEq]
    exact v.original_choice_replay P h width r banks source table target owners
      (dims).words.addresses (dims).copies size input π auth extent heap mountedAll t c next

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
