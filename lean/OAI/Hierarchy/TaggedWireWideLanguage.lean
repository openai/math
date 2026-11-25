import OAI.Hierarchy.TaggedWireWideAdmission
import OAI.Hierarchy.ProbeFixedWideAlphabetOrigin

namespace OAI
/-! # Every original admissible tape encodes one complete routed branch -/

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
local notation "slots" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "order" => wideRouteOrder h D k


variable (size : ℕ)
  (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size)
  (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (seed : Boot.Tape h (2^v.W))
  (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "mid" => v.wideSignedMidAt h width size stock M π order

include extent
attribute [local irreducible] CalendarTape.Path CalendarTape.encode CalendarTape.bits

set_option cleanup.letToHave false in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wide_tape_admission (raw : Bits (CalendarTape.bits (X := Boot.Tape h (2^v.W)) (reader).format.slot es)) :
    admissible C es (mid ((L).header es raw seed)) ↔
      ∃! j : CalendarTape.Path (X := Boot.Tape h (2^v.W)) (reader).format.slot es (mid seed),
        (CalendarTape.encode (X := Boot.Tape h (2^v.W)) (reader).format.slot es (mid seed)).toFun j=raw := by
  let header : Boot.Tape h (2^v.W) := (L).header es raw seed
  have alphabets := v.wide_alphabet_origin_at h width size extent stock M π order header
  have admission := v.wide_tape_admission_origin h width size extent M π seed age budget small raw
  exact admission alphabets

omit extent in
private theorem admitted_embedding_image {α β : Type*} (code : α ↪ β) (accepts : β → Prop)
    (admission : ∀ raw, accepts raw ↔ ∃! a : α, code a = raw) (a : α) :
    accepts (code a) :=
  (admission (code a)).2 ⟨a, rfl, fun _ same => code.injective same⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wide_encoded_path (j : CalendarTape.Path (reader).format.slot es (mid seed)) :
    admissible C es (mid ((L).header es (CalendarTape.encode (reader).format.slot es (mid seed) j) seed)) :=
  @admitted_embedding_image (CalendarTape.Path (reader).format.slot es (mid seed))
    (Bits (CalendarTape.bits (reader).format.slot es))
    (CalendarTape.encode (reader).format.slot es (mid seed))
    (fun raw => admissible C es (mid ((L).header es raw seed)))
    (v.wide_tape_admission h width size extent M π seed age budget small) j

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
