import OAI.Hierarchy.ProbeFixedWideEventCode
import OAI.Hierarchy.ProbeFixedWideSignedOutput
import OAI.Hierarchy.ProbeFixedPaidMountedBoot
import OAI.Hierarchy.ProbeFixedWidePaidOperands
import OAI.Hierarchy.ProtocolRAMCoreRouteSafe

namespace OAI
/-! # Original paid width transactions on the finite input used by the signed settlement -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StockCommit
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A))
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "src" => TerminalLayout.source page
local notation "tab" => TerminalLayout.table page
local notation "dst" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "order" => wideRouteOrder h D k
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "route" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (directory).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "C" => v.wideSignedChart h width stock

/-- The two low public directories installed for forest, commodity and boundary rows. -/
def widePairedWords (raw : Boot.Tape h D) : Boot.Tape h D :=
  PaidPairDirectory.mount (v.catalystPairOwners P h width) (v.catalystPairParity P h width) r raw

open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open ThreeFlat.RAM

private theorem segment_cell {W x : ℕ} (base rows : ℕ) (value : ℕ→Word W) (m m' : Memory W)
    (same : m x=m' x) : fillSegment base rows value m x=fillSegment base rows value m' x := by
  unfold fillSegment
  split <;> first | rfl | exact same

private theorem pages_cell {W x : ℕ} (ps : List RoleROM.Page) (base : ℕ) (m m' : Memory W)
    (same : m x=m' x) : RoleROM.publish base ps m x=RoleROM.publish base ps m' x := by
  induction ps generalizing base with
  | nil => exact same
  | cons p ps ih =>
    apply segment_cell
    exact ih (base+p.rows)

theorem role_cell (bank : Bank) (ss : List PaidWidths.Slice) (raw raw' : Boot.Tape h D)
    (x : ℕ) (same : raw x=raw' x) :
    v.wideRoleWords h width bank ss raw x=v.wideRoleWords h width bank ss raw' x := by
  unfold wideRoleWords RoleRoom.mountStocks RoleRoom.mount
  apply pages_cell
  apply segment_cell
  exact pages_cell _ _ raw raw' same

theorem paired_cell (raw raw' : Boot.Tape h D) (x : ℕ) (same : raw x=raw' x) :
    v.widePairedWords h width raw x=v.widePairedWords h width raw' x := by
  unfold widePairedWords PaidPairDirectory.mount RepairHistogram.pairAdvice
  apply segment_cell
  exact segment_cell _ _ _ _ _ same

/-- The original low ordinal/parity pages and the entire high signed-role and
retained-stock table can be serialized in either order at every input address. -/
theorem wide_role_pair_words (bank : Bank) (ss : List PaidWidths.Slice) (raw : Boot.Tape h D) :
    v.wideRoleWords h width bank ss (v.widePairedWords h width raw)=
      v.widePairedWords h width (v.wideRoleWords h width bank ss raw) := by
  let high:=v.wideRoleStart h width bank ss
  let occ:=v.catalystPairOwners P h width
  let par:=v.catalystPairParity P h width
  have span : 2*r≤occ.size := (Nat.lt_log2_self (n:=2*r)).le
  have tagSpan : 2*r≤par.size := (Nat.lt_log2_self (n:=2*r)).le
  have middle : occ.base+occ.size=par.base:=rfl
  have stop : par.base+par.size=start:=rfl
  have early : start≤(A).first:=v.catalyst_static_before P h width
  have first : (A).first≤(A).endAddress v.mesh:=Nat.le_add_right ..
  have last : (A).endAddress v.mesh≤high:=le_max_left ..
  have low (m : Boot.Tape h D) (x : ℕ) (hx : x<high) :
      v.wideRoleWords h width bank ss m x=m x :=
    RoleRoom.stocks_below v.sampler (v.wideOrder h width) directory (P).catalogue.rows high x m hx
  have above (m : Boot.Tape h D) (x : ℕ) (hx : high≤x) :
      v.widePairedWords h width m x=m x := by
    apply PaidPairDirectory.frame occ par r
    rintro (⟨_,hi⟩|⟨_,hi⟩) <;> omega
  funext x
  rcases lt_or_ge x high with lo|hi
  · rw [low _ x lo]
    exact paired_cell v h width _ _ x (low raw x lo).symm
  · rw [above _ x hi]
    exact role_cell v h width bank ss _ _ x (above raw x hi)

/-- Five chronological width sources share the original ABI for edge labels and
the actual retained commodity inventory slot order. -/

theorem wide_paid_mounted_at (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (maxBroadcastBits : ℕ)
    (age : v.wideSignedHeight≤h) (budget : v.keepLimit*width+1≤2^h)
    (mounted : Calendar.mounted C (events v.mesh)
      (v.wideSignedMidAt h width size stock M π order (v.widePairedWords h width raw))) :
    PaidWidths.Mounted (banks).width (P).catalogue.rows src (v.widePaidSlices h width maxBroadcastBits)
      (v.wideSignedCheckoutAt h width size stock M π order (v.widePairedWords h width raw)) := by
  have geometry:=v.wideGeometryPrefix h width
  have room:=v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width) age budget
  let markets:=v.catalystMarkets P h width
  let layout:=v.catalyst_market_layout_at P h width size geometry.2.1 extent
  let bankEnd:=v.catalyst_static_end P h width A
  have first : (A).first≤(A).endAddress v.mesh:=Nat.le_add_right ..
  have upper : (A).endAddress v.mesh≤(banks).width.base := by
    have high : TerminalLayout.footprint v.mesh A stock
      (ownerRowFactor D k v.sampler.degree v.depth (max (Fintype.card (StripDirectory.PayloadRole N k))
        (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h) (P).catalogue.rows r
      (Fintype.card (Columns h D)*k) cnt<2^page:=Nat.lt_log2_self
    change (A).endAddress v.mesh≤1*2^page
    unfold TerminalLayout.footprint at high
    omega
  have fits : (banks).width.base<2^w:=by
    have hi : 28*2^page<2^w:=room.1
    change 1*2^page<2^w
    omega
  have safe:=CoreRoute.source_safe v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
    (directory).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k) w (banks).width.base
    (geometry.2.2.trans ((v.catalyst_initial_le_first P h width).trans (first.trans upper))) fits
  apply v.paid_booted_mount h width (P).joint (P).catalogue (v.wideOrder h width) M (WideMemory.groups h v.W)
    directory (v.wideSources h width).2 π stock maxBroadcastBits order markets raw layout
    room.1 (bankEnd.le.trans (first.trans extent))
    (fun i=>bankEnd.le.trans (v.catalyst_market_low P h width i)) geometry.1 geometry.2.1 geometry.2.2 mounted safe
  intro a live
  obtain ⟨edge,tree,source,mate⟩:=v.wide_paid_operands h width banks src tab dst owners a live room.2
  refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ upper edge,ProtocolRAMGeneratedWrite.fits_mono _ upper tree,
    ProtocolRAMGeneratedWrite.fits_mono _ upper source,?_⟩
  rintro ⟨mask,other⟩ included
  have hm : (v.nativeTrees P h width a).catalystMate=some (mask,other):=included
  have fields:=mate mask other hm
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ upper fields.1,ProtocolRAMGeneratedWrite.fits_mono _ upper fields.2⟩

set_option cleanup.letToHave false in
set_option maxHeartbeats 1000000 in
/-- The signed reporter consumes precisely the actual width transactions mounted by
the same original program, including the pair directories supplied at boot. -/
abbrev wide_paid_run_at :=
  fun (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (maxBroadcastBits : ℕ)
    (age : v.wideSignedHeight≤h) (small : width≤2^h) (budget : v.keepLimit*width+1≤2^h)
    (state : Word w) (mounted : Calendar.mounted C (events v.mesh)
      (v.wideSignedMidAt h width size stock M π order (v.widePairedWords h width raw))) =>
    let paired := v.widePairedWords h width raw
    let slices := v.widePaidSlices h width maxBroadcastBits
    have receipt : PaidWidths.Mounted (banks).width (P).catalogue.rows src slices
        (v.wideSignedCheckoutAt h width size stock M π order paired) :=
      v.wide_paid_mounted_at h width size extent M π raw maxBroadcastBits age budget mounted
    let run := v.wide_retained_run_at h width size extent M π paired slices age small budget state mounted
    run receipt

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
