import OAI.Hierarchy.ProbeFixedWideFundedPrefix
import OAI.Hierarchy.ProbeFixedCatalystMemoryUpper

namespace OAI
/-! # Fresh fixed-ROM words above the entire authenticated original settlement -/
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

theorem wide_funded_raw_above (x : ℕ) (above : full≤x) : seed x=raw x := by
  let z:=sizes
  have ordered : hi≤z.stop hi ∧ 7*z.old≤z.stop hi := by
    dsimp only [RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,RoleRoom.Sizes.axis,
      RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
    omega
  have afterStock : z.stop hi+2*z.old≤x := by change 3*(z.stop hi+1)≤x at above;omega
  change RoleRoom.mountStocks v.sampler order directory rows hi (v.widePairedWords h width raw) x=_
  unfold RoleRoom.mountStocks
  rw [RoleRoom.outside v.sampler order directory rows hi x _ (.inr (by
    change z.stop hi≤x
    omega))]
  rw [RoleROM.publish_frame _ _ _ _ (.inr (by
    change z.stop hi+(z.old+(z.old+0))≤x
    omega))]
  let occ:=v.catalystPairOwners P h width
  let par:=v.catalystPairParity P h width
  have span : 2*r≤occ.size:=Nat.lt_log2_self.le
  have tagSpan : 2*r≤par.size:=Nat.lt_log2_self.le
  have middle : occ.base+occ.size=par.base:=rfl
  have stop : par.base+par.size=start:=rfl
  have early : start≤(A).first:=v.catalyst_static_before P h width
  have first : (A).first≤(A).endAddress v.mesh:=Nat.le_add_right ..
  have arenaBefore : (A).endAddress v.mesh≤hi:=le_max_left ..
  apply PaidPairDirectory.frame occ par r
  rintro (⟨_,u⟩|⟨_,u⟩) <;> omega

private theorem cast_reserve_output {wordBits entries n count : ℕ} (a : ReserveUse.Archive) (b : RouteSettlement.Banks)
    (cap : ℕ) (site : Fin entries→Fin count) (bits : Fin entries→ℕ) (m : Memory wordBits) (eq : entries=n) :
    ReserveUse.output a b cap (fun i=>site (Fin.cast eq.symm i)) (fun i=>bits (Fin.cast eq.symm i)) m=
      ReserveUse.output a b cap site bits m := by cases eq; rfl

/-- The true CPU memory image can retain additional costed public tables at every
address beyond all the signed input/settlement pages and below the enlarged header size. -/
theorem wide_settled_seed (extendsTape : full ≤ size) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    {entries : ℕ} (card : entries=cnt) (site : Fin entries→Fin num) (debit : Fin entries→ℕ)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin rows)} {center : J→List (Fin rows)}
    (route : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (x : ℕ) (above : hi≤x) (inTape : x<size) :
    let archive:=result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
    (sink).output (ReserveUse.output original old supply site debit archive) route ci cj x=seed x := by
  intro archive
  let high:=hi
  have top : TerminalLayout.extent page ss≤high:=le_max_right ..
  have prior : (A).endAddress v.mesh≤high:=le_max_left ..
  have e:=v.wide_funded_extent h width bits
  have room:=(v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width) ((le_max_left ..).trans height) budget).2
  have first : (A).first<2^w:=(Nat.le_add_right ..).trans_lt room
  have boot:=v.wide_signed_boot_above h width stock M π o seed size (e.trans extendsTape) first
  have mounted:=(v.wide_funded_stock_at_size h width M π raw bits size extendsTape height budget small).mounted_all
  have paid:=v.wide_funded_paid_at_size h width M π raw bits size extendsTape height budget small
  have same := v.catalyst_upper P h width L stock stride start supply v.wideJobs
    (fun i=>site (Fin.cast card.symm i)) (fun i=>debit (Fin.cast card.symm i))
    (routeBanks start cnt r) g route ci cj mid ss x rfl
    (fun e _=>ledger_owner_rows s v.mesh (P).catalogue (P).routes F _ e)
    (top.trans above) mounted paid
  change (sink).output (ReserveUse.output original old supply
    (fun i=>site (Fin.cast card.symm i)) (fun i=>debit (Fin.cast card.symm i)) archive) route ci cj x=mid x at same
  rw [cast_reserve_output original old supply site debit _ card] at same
  exact same.trans (boot.2 x (prior.trans above) inTape)

theorem wide_settled_above (extendsTape : full ≤ size) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
    {entries : ℕ} (card : entries=cnt) (site : Fin entries→Fin num) (debit : Fin entries→ℕ)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin rows)} {center : J→List (Fin rows)}
    (route : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (x : ℕ) (above : full≤x) (inTape : x<size) :
    let archive:=result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows (TerminalLayout.source page) ss chk))
    (sink).output (ReserveUse.output original old supply site debit archive) route ci cj x=raw x := by
  intro archive
  have endAt : hi≤full := by
    change hi ≤ (sizes).ceiling hi
    dsimp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,
      RoleRoom.Sizes.axis,RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
    omega
  exact (v.wide_settled_seed h width size M π raw bits extendsTape height budget small card site debit
    route ci cj x (endAt.trans above) inTape).trans (v.wide_funded_raw_above h width raw bits x above)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
