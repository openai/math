import OAI.Hierarchy.ProbeFixedWideStockRun
import OAI.Hierarchy.ProbeFixedWidePrivateHeader
import OAI.Hierarchy.TaggedWireFixedAdmission

namespace OAI
/-! # The authentic signed calendar and its original private selector language -/

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


def wideSelector (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) :=
  let sizes:=v.wide_stock_sizes h width age budget small
  v.nativeSelector P h width r banks source table target owners sizes.words.addresses sizes.copies

variable (size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh≤ size) (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h (2^v.W)) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows
local notation "mid" => v.wideSignedMidAt h width size stock M π order

include extent
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem wide_tape_admission_origin (raw : Bits (CalendarTape.bits (reader).format.slot es))
    (origin : (E).menus.leftAlphabet.Capped v.menu.alphabet (mid ((L).header es raw seed)) ∧
      (E).menus.rightAlphabet.Capped v.menu.alphabet (mid ((L).header es raw seed))) :
    admissible C es (mid ((L).header es raw seed)) ↔
      ∃! j : CalendarTape.Path (reader).format.slot es (mid seed),
        CalendarTape.encode (reader).format.slot es (mid seed) j=raw := by
  have sizes:=v.wide_stock_sizes h width age budget small
  let base:=v.wideSignedWords h width stock M π order seed
  have commute (x : Bits (CalendarTape.bits (reader).format.slot es)) :
      mid ((L).header es x seed)=Boot.booted (v.catalystMarkets P h width) size ((L).header es x base) := by
    exact congrArg (Boot.booted (v.catalystMarkets P h width) size)
      (v.wide_signed_header h width stock M π order r banks source table target owners
        sizes.words.addresses sizes.copies x seed)
  have allRuns (x : Bits (CalendarTape.bits (reader).format.slot es)) :
      Calendar.mounted C es (Boot.booted (v.catalystMarkets P h width) size ((L).header es x base)) := by
    rw [←commute]
    exact (v.wide_stock_at h width size extent M π ((L).header es x seed) age budget small).mounted_all
  have placement:=v.wideGeometryPrefix h width
  let coreStart:=CoreCatalogue.top h v.W (WideMemory.K h v.W) (WideMemory.dir h v.W k v.wideJobs).groups
    (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
  have keyEnd:=(Public.borders v.sampler coreStart h v.W k v.wideJobs v.depth).2
  have dir : (StripDirectory.stratumHeader h D k v.sampler.degree v.depth (P).routes.directory.keysBase).stop≤(P).joint.initial :=
    keyEnd.trans ((Nat.le_add_right ..).trans placement.2.2)
  have hfit : h<2^w := (Nat.lt_two_pow_self (n:=h)).trans (v.date_prefix_fit h)
  have cap : v.menu.maximum<2^w :=
    (((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans sizes.market)).trans_lt hfit)
  rw [commute] at origin ⊢
  exact v.tape_admission_at P h width r banks source table target owners sizes.words.addresses
    sizes.copies size extent π base (v.wide_signed_words_authentic h width stock M π order seed)
    raw placement.2.1 dir cap sizes.words.cut (by
      have alphabet := (v.catalogue_words (v.seed P h width) width).1
      constructor
      · intro x lo hi
        exact (origin.1 x lo hi).trans alphabet.symm.le
      · intro x lo hi
        exact (origin.2 x lo hi).trans alphabet.symm.le) allRuns



end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
