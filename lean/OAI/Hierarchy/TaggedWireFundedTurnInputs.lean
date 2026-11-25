import OAI.Hierarchy.TaggedWireWidePaidShelf
import OAI.Hierarchy.TaggedWireFundedRoleOutput
import OAI.Hierarchy.TaggedWireRolesAfterReplay
import OAI.Hierarchy.ProbeFixedWidePrefixUpper
import OAI.Hierarchy.ProbeFixedWideSignedHeader

namespace OAI
/-! # The original turn operands on the funded, dated replay -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram
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

local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups H R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups H R
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups H

/-- All signed role, site, and inventory operands at once, after the real
settlement and a bounded prefix replay. This uses no independently supplied
lookup table, permutation, purchased endpoint or site interpretation. -/
theorem wide_funded_turn_inputs (extendsTape : full≤ size) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    {entries : ℕ} (card : entries=cnt) (owner : Fin entries→Fin num) (debits : Fin entries→ℕ)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin rows)} {center : J→List (Fin rows)}
    (route : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (m : Memory w) :
    let archive:=result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
    let out:=(sink).output (ReserveUse.output original old supply owner debits archive) route ci cj
    (∀x,x<full→m x=out x) →
    (RoleRoom.tables v.sampler order directory rows).Resident hi m ∧ SiteROM.Resident directory ((sizes).offset hi) m ∧
    RoleRoom.StockResident (h:=h) (W:=v.W) (k:=k) (edges:=rows) ((sizes).stop hi) m ∧
    CoreRoute.Seen order M (WideMemory.groups h v.W) directory (v.wideSources h width).2 v.depth π m ∧
    CoreCatalogue.Header order coreHead v.wideJobs (CoreCatalogue.groupStart h v.W) M m ∧
    (∀j : Fin v.wideJobs,∀i : Key h D k,((pub).shelf j).PortData v.sampler π v.depth i m) ∧
    ∀x,x<(A).endAddress v.mesh→m x=chk x := by
  subst entries
  intro archive out keep
  have extent:=v.wide_funded_extent h width bits
  have upto:=extent.trans extendsTape
  have word:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width) ((le_max_left ..).trans height) budget).2
  have first : (A).first≤(A).endAddress v.mesh:=Nat.le_add_right ..
  have mounted:=(v.wide_funded_stock_at_size h width M π raw bits size extendsTape height budget small).mounted_all
  have paid:=v.wide_funded_paid_at_size h width M π raw bits size extendsTape height budget small
  have ⟨roles,sites,inventory⟩:=v.wide_signed_role_output_at h width stock M π o
    (v.widePairedWords h width raw) ss owner debits route ci cj size extendsTape (first.trans_lt word) mounted paid
  have ⟨roles',sites',inventory'⟩:=RoleRoom.after_replay v.sampler order directory rows hi roles sites inventory keep
  have «prefix»:=v.wideGeometryPrefix h width
  have geo:=«prefix».2.2.trans (v.catalyst_initial_le_first P h width)
  have checkedLow (x) (inside:x<(A).endAddress v.mesh) : m x=chk x := by
    have level : TerminalLayout.footprint v.mesh A stock stride rows r num cnt<2^page:=Nat.lt_log2_self
    unfold TerminalLayout.footprint at level
    have xpage : x<2^page:=by omega
    exact (keep x (inside.trans_le extent)).trans (TerminalLayout.settled_below_at v.mesh A (P).catalogue L stock stride
      start cnt supply owner debits v.sampler v.wideJobs (routeBanks start cnt r) g route ci cj chk ss x rfl xpage paid)
  have low (x) (small:x<(A).first) : m x=mid x:=
    (checkedLow x (small.trans_le first)).trans (v.wide_signed_checkout_below h width stock M π o seed size x small mounted)
  have boot:=v.wide_signed_boot_at h width size upto stock M π o seed word
  have retained:=boot.2.2.1.frame (geo.trans_lt (first.trans_lt word)) (fun x inside=>low x (inside.trans_le geo))
  have head:=v.wide_signed_header_at h width size upto stock M π o seed word low
  exact ⟨roles',sites',inventory',retained,head,
    v.wide_paid_shelf_read h width size upto M π seed m word mounted checkedLow,checkedLow⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
