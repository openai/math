import OAI.Hierarchy.ProbeFixedWidePrefixHigh

namespace OAI
/-! # The original paid terminal starting at the full certified post-subdivision memory -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
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



open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "order" => v.wideOrder h width
local notation "sizes" => RoleRoom.shape (R:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "sheet" => v.wideSignedPage h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (bits : ℕ)
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits


theorem wide_funded_tail_exec (extendsTape : full ≤ size) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    {dates : Dates C mid L pay num width} {pos : 0<num}
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin rows)} {center : J→List (Fin rows)}
    {enum : Fin r≃RouteOccurrence core center} {ci : I→ℕ} {cj : J→Fin num} :
    let issues:=CatalystArchive.issued dates
    let owner:=CatalystArchive.nativeSite L v.mesh issues pos chk
    let amounts:=CatalystArchive.debit v.mesh issues
    let archive:=result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
    let settled:=(sink).output (ReserveUse.output original old supply owner amounts archive) enum ci (fun j=>(cj j).val)
    Whole.Reconciliation sink original supply owner amounts enum ci cj archive →
    (CatalystArchive.terminal C L routes ((A).endAddress v.mesh) sink (TerminalLayout.source page) ss original num cnt supply).Exec mid
      settled (CatalystArchive.terminalTime C L routes sink ss original num cnt supply) := by
  intro issues owner amounts archive settled certificates
  have good:=(v.wide_funded_stock_at_size h width M π raw bits size extendsTape height budget small).mounted_all
  have paid:=v.wide_funded_paid_at_size h width M π raw bits size extendsTape height budget small
  have room:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width) ((le_max_left ..).trans height) budget).1
  have geo:=TerminalLayout.allocated v.mesh A L (P).catalogue h v.W k num cnt start stride w stock rfl
    (v.catalyst_static_end P h width A).le (v.wide_geometry_at_page h width stock stride start num cnt room) room
  have positive : 0<w:=by unfold Native.wordBits;omega
  have flag:=historyFlag_fits_of_dated C A positive (fun t _=>v.catalyst_dated_verdict P h width r old
    (TerminalLayout.source page) (TerminalLayout.table page) (TerminalLayout.destination page) (sinkBank start cnt r rows) t)
  have first : (A).endAddress v.mesh<2^w:=by have:=geo.flagWord;omega
  have incomingReads (e : Event) (inMesh : e∈events v.mesh) : ((L).term e).Fits w (L).arena.first := by
    obtain ⟨i,eventEq⟩:=List.mem_iff_get.mp inMesh
    have args:=v.catalyst_owner_args h width _ _ _ _ (P).joint (P).catalogue (v.wideSources h width).2 own
      (v.wideGeometryPrefix h width).2.2 first i
    rw [eventEq] at args
    exact ProtocolRAMGeneratedWrite.fits_mono _ (((Nat.le_add_right ..).trans
      ((A).within v.mesh e inMesh)).trans geo.flagLow.1.le) args
  have word : (old).kind.base<2^w := by
    have bankOrder : (old).kind.base+2*r≤(old).index.base := geo.order
    have indexFits : (old).index.base+2*r<2^w := geo.indexWord
    omega
  have safe:=CoreRoute.source_safe v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
    (directory).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k) w (old).kind.base
    ((v.wideGeometryPrefix h width).2.2.trans ((v.catalyst_initial_le_first P h width).trans geo.refOrder)) word
  have fit:=CoreRoute.pass_fits (routeBanks start cnt r) g old safe
    ⟨geo.recipes .kind,geo.recipes .mode,geo.recipes .operand⟩ geo.order geo.indexWord
  let invoice (n : ℕ) : Prop := (CatalystArchive.terminal C L routes ((A).endAddress v.mesh) sink (TerminalLayout.source page) ss original num n supply).Exec mid
    settled (CatalystArchive.terminalTime C L routes sink ss original num n supply)
  have honest : invoice (recordCount v.mesh issues) :=
    CatalystArchive.terminal_exec C L routes ((A).endAddress v.mesh) sink (TerminalLayout.source page) ss original
      issues pos fit enum ci cj mid good flag geo.flagWord geo.widthRoom
      (fun e _=>ledger_owner_rows s v.mesh (P).catalogue (P).routes F own e) incomingReads geo.ownerEnd paid certificates
  have card : recordCount v.mesh issues=cnt:=recordCount_rowOnly v.mesh issues decl (issued_rows dates)
  change invoice cnt
  rw [← card]
  exact @honest

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
