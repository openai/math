import OAI.Hierarchy.ProbeFixedWideSignedBoot
import OAI.Hierarchy.ProtocolRAMCatalystArchiveMasterAll

namespace OAI
/-! # The original kind and pointer entries in the checked fixed signed calendar -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
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
  (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h



/-- Both chronological pointers and their parity have been genuinely mounted in the same
finite boot tape as the selector and signed menu, and survive the complete calendar pass. -/
abbrev wide_signed_origin_at (size : ℕ) (extent : (A).endAddress v.mesh ≤ size) (stock : Bank) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k) (raw : Boot.Tape h D)
    (room : (A).endAddress v.mesh<2^w) :=
  let bits:=v.wideSignedPage h width stock
  let C:=v.wideSignedChart h width stock
  let b:=TerminalLayout.settlement bits stock
  let owners:=sinkBank start cnt r (P).catalogue.rows
  let mid:=v.wideSignedMidAt h width size stock M π o raw
  let boot:=v.wide_signed_boot_at h width size extent stock M π o raw room
  have stop:=v.catalyst_static_end P h width A
  fun (ok : Calendar.mounted C (events v.mesh) mid) =>
    boot.2.2.2.2.2.2.2.2 C A ((A).endAddress v.mesh) stop.le
      (.inr (stop.le.trans (Nat.le_add_right ..)))
      (fun e x hx=>(v.event_prefix P h width r b (TerminalLayout.source bits) (TerminalLayout.table bits)
        (TerminalLayout.destination bits) owners e x hx).1) ok

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
