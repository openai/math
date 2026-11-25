import OAI.Hierarchy.TaggedWireWidePaidRead
import OAI.Hierarchy.TaggedWireRolesAfterReplay
import OAI.Hierarchy.ProbeFixedWideReplayedTurn

namespace OAI
/-! # The native live turn after the signed chronological paid-width replay -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open CatalystArchive StripChart CatalogueRows ColumnWires
open BoughtSockets CoreRoute PurchaseCT ProtocolRAMEmit WireTelescope
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
variable (h width : ℕ)
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "G" => (directory).groups
local notation "rows" => (P).catalogue.rows
local notation "N" => Fintype.card (Old h v.W k rows)
local notation "z" => RoleRoom.shape («R»:=R) v.sampler directory rows
local notation "base" => CoreCatalogue.headBase h v.W K G H
local notation "sites" => CoreCatalogue.siteBase h v.W K
local notation "super" => CoreCatalogue.superStart h v.W
local notation "bits" => CoreCatalogue.pointBits h v.W
local notation "published" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K G H R

local notation "order" => v.wideOrder h width
local notation "groups" => WideMemory.groups h v.W
local notation "head" => (published).header h D k v.sampler.degree v.depth

variable (ss : List PaidWidths.Slice) (workStart : ℕ)
local notation "stock" => v.fixedTerminalStock P h width
local notation "high" => v.wideRoleStart h width stock ss
local notation "size" => v.wideRoleSize h width stock ss
local notation "out" => workStart
local notation "lw" => v.wideWidthLayout h width ss
local notation "paidBank" => (lw).bank (events v.mesh).length
local notation "purse" => TerminalLayout.settlement (v.wideSignedPage h width stock) stock
local notation "tr" => RoleRoom.turnBoard («R»:=R) v.sampler directory (edges:=rows) high out (P).catalogue.core (v.widePaidPorts h width high)
local notation "inv" => Inventory.ofOriginal ((z).stop high) N paidBank stock (purse).reserved (purse).used
local notation "axes" => Fintype.card (Columns h D)*k

/-- Run all eleven role/width/coordinate writes on the actual last paid-width
page and the original inventory and physical slot tables retained by replay. -/
theorem wide_signed_turn_live_at (M : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)
    {word : Fin rows→Row} {amount : Fin rows→ℕ}
    (A₀ : CatalogueRows.Alignment (P).catalogue v.sampler π v.depth marks M word amount
      ((P).catalogue.original v.sampler π v.depth marks order (v.wideBoughtOrdinal h width π marks)))
    (m : Boot.Tape h D)
    (roles : (RoleRoom.tables v.sampler order directory rows).Resident high m)
    (site : SiteROM.Resident directory ((z).offset high) m)
    (inventory : RoleRoom.StockResident (h:=h) (W:=v.W) (k:=k) (edges:=rows) ((z).stop high) m)
    (header : CoreCatalogue.Header order base v.wideJobs (CoreCatalogue.groupStart h v.W) M m)
    (core : CoreRoute.Seen order M groups directory (v.wideSources h width).2 v.depth π m)
    (shelf : ∀e : Bought v.sampler π v.depth marks,
      ((published).shelf e.1).PortData v.sampler π v.depth (BoughtLocation.keyOf e.2) m)
    (issued : Attempt→CatalystArchive.Entry axes width)
    (counters : ∀j:Fin axes,
      RouteSettlement.actual (purse).used m j.val=usedAt (CatalystArchive.site v.mesh issued) (debit v.mesh issued) j ∧
      RouteSettlement.actual (purse).reserved m j.val=fuel v.mesh*width)
    (enough : ∀e:Fin rows,((paidBank).read m (e.val:Word w)).val≤amount e)
    (afterReplay : v.wideReplayedTurnBase h width ss≤out) (fits : out+7*N+4*rows<2^w)
    (rootFit : CoreCatalogue.top h v.W K G H R<2^w)
    (jobs : v.wideJobs≤2^w) (keyFit : PurchaseFrozen.count h D k≤2^w)
    (tileFit : (v.depth+1)*PurchaseFrozen.paths h v.sampler.degree v.depth≤2^w) :
    let fixed:=fun e:Fin rows=>((paidBank).read m (e.val:Word w)).val
    let goods:=fun i:Goods h v.W k=>((stock).read m ((PurchaseInventory.slot i:ℕ):Word w)).val
    let old:=SettledMatrix.Layout.bits fixed goods (fun _:Catalysts h v.W k=>fuel v.mesh*width) (RoleRoom.usedBy v.mesh issued)
    let ports:=livePort v.sampler (P).catalogue π marks unique order (v.wideBoughtOrdinal h width π marks) A₀
    let before:=fun (i : Fin N) (_:0<old i) side=>publicRoleFor v.sampler π (activePaid v.sampler amount ports)
      (SettledMatrix.Layout.numbered i) side
    ((tr).extended inv w).Exec m ((tr).extendedState inv m) ((tr).extendedTime inv) ∧
      Board.LiveReads v.sampler tr old amount before (fun i hi s=>.inl (ports i hi s)) ((tr).extendedState inv m) := by
  intro fixed goods old ports before
  have origin:=v.wide_replayed_start h width ss
  have ready:=v.wide_signed_turn_ready_at h width stock paidBank ss workStart
    (v.fixedTerminalStock_end P h width) (origin.1.trans afterReplay) (origin.2.trans afterReplay) fits
  have big : out+7*N+4*rows<2^w:=fits
  have highFit : (z).ceiling high<2^w:=origin.1.trans_lt (by omega)
  have pub : (z).publicRows≤(z).ceiling high ∧ (z).signedSites≤(z).ceiling high := by
    simp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,
      RoleRoom.Sizes.axis,RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
    omega
  have ax : (siteLast h D k+1)*(2*k)≤2^w:=pub.2.trans highFit.le
  have factor : 1≤2*k:=by have hk:=v.positive; omega
  have siteCountBound : siteLast h D k+1≤2^w :=
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (siteLast h D k+1) factor : _≤_).trans ax
  have wide : 4≤2^w:=by
    have low : 4≤(z).ceiling high := by
      have nonzero : 0<(z).signedSites := Nat.mul_pos (Nat.succ_pos _) (by omega : 0<2*k)
      unfold RoleRoom.Sizes.ceiling RoleRoom.Sizes.stop RoleRoom.Sizes.offset RoleRoom.Sizes.positive
        RoleRoom.Sizes.axis RoleRoom.Sizes.ext RoleRoom.Sizes.free RoleRoom.Sizes.pub
      omega
    exact low.trans highFit.le
  have room : (tr).endAt+3*N<2^w:=by
    change (out+4*N+4*rows)+3*N<2^w
    omega
  have perm (j : Fin (2^h)) : m j.val=((π j).val:Word w):=by
    have atKey:=core.board.input j
    change m (0+(j.val:Word w).val%2^h)=_ at atKey
    rw [Fin.val_cast_of_lt (j.isLt.trans (v.date_prefix_fit h)),Nat.mod_eq_of_lt j.isLt,Nat.zero_add] at atKey
    exact atKey
  apply RoleRoom.settled_live_ready v.sampler order directory high out (P).catalogue.core (v.widePaidPorts h width high)
    paidBank stock purse π m roles inventory core.board.rows perm siteCountBound wide room ready.1 ready.2
    (pub.1.trans highFit.le) ax (v.date_prefix_fit h).le v.mesh issued counters amount enough ports
  exact v.wide_resolved_paid h width high M π marks unique A₀ m header core roles site shelf rootFit highFit
    (by omega) jobs keyFit tileFit

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
