import OAI.Hierarchy.ProbeFixedWideSignedOutput

namespace OAI
/-! # The role pages retained by the signed program with a larger original header -/

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



open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "order" => v.wideOrder h width
local notation "sizes" => RoleRoom.shape (R:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "sheet" => v.wideSignedPage h width

theorem wide_signed_role_output_at (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k)
    (raw : Boot.Tape h D) (slices : List PaidWidths.Slice) (site : Fin cnt→Fin num) (debit : Fin cnt→ℕ)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin rows)} {center : J→List (Fin rows)}
    (route : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (size : ℕ) (fits : v.wideRoleSize h width stock slices≤ size) (room : (A).first<2^w) :
    let page:=sheet stock
    let high:=v.wideRoleStart h width stock slices
    let input:=v.wideRoleWords h width stock slices raw
    let actual:=v.wideSignedWords h width stock M π o input
    let mid:=Boot.booted (v.catalystMarkets P h width) size actual
    let L:=ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
    let b:=TerminalLayout.settlement page stock
    let a:=TerminalLayout.reserve start cnt page
    let src:=TerminalLayout.source page
    let owners:=sinkBank start cnt r rows
    let sink:=(P).catalogue.sink r b src (TerminalLayout.table page) (TerminalLayout.destination page) owners
    let C:=v.wideSignedChart h width stock
    let checked:=v.wideSignedCheckoutAt h width size stock M π o input
    let g:=CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
      (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
    let recipes:=routeBanks start cnt r
    let moves:=CoreRoute.stages b recipes g v.sampler h v.W k v.wideJobs
    let archive:=result moves (result (L.scans v.mesh num) (PaidWidths.output b.width rows src slices checked))
    let output:=sink.output (ReserveUse.output a b (fuel v.mesh*width) site debit archive) route ci cj
    Calendar.mounted C (events v.mesh) mid → PaidWidths.Mounted b.width rows src slices checked →
      (RoleRoom.tables v.sampler order directory rows).Resident high output ∧
      SiteROM.Resident directory ((sizes).offset high) output ∧
      RoleRoom.StockResident (h:=h) (W:=v.W) (k:=k) (edges:=rows) ((sizes).stop high) output := by
  intro page high input actual mid L b a src owners sink C checked g recipes moves archive output live funded
  have extent : (A).endAddress v.mesh≤high := le_max_left ..
  have term : TerminalLayout.extent page slices≤high := le_max_right ..
  have span : high≤(sizes).ceiling high := by
    dsimp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,
      RoleRoom.Sizes.axis,RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
    omega
  have run:=v.wide_signed_boot_above h width stock M π o input size (extent.trans (span.trans fits)) room
  apply RoleRoom.retained v.sampler order directory rows high raw output
  intro x lo hi
  have settled:=v.catalyst_upper P h width L stock stride start (fuel v.mesh*width) v.wideJobs site debit
    recipes g route ci cj mid slices x rfl (fun e _=>ledger_owner_rows s v.mesh (P).catalogue (P).routes F _ e)
    (term.trans lo) live funded
  exact settled.trans (run.2 x (extent.trans lo) (hi.trans_le fits))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
