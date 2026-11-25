import OAI.Hierarchy.ProbeFixedWideSignedFits
import OAI.Hierarchy.ProbeFixedWideSignedHeader
import OAI.Hierarchy.TaggedWirePaidSelection
import OAI.Hierarchy.ProbePublicStageCount

namespace OAI
/-! # Original paid socket operands on the authentic signed placement -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open CatalystArchive StripChart CatalogueRows ColumnWires
open BoughtSockets CoreRoute PurchaseCT ProtocolRAMEmit
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

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wide_resolved_paid
    (start M : ℕ) (π : Equiv.Perm (Fin (2^h))) (marks : Marks h v.W k v.wideJobs)
    (unique : Exclusive marks) {word : Fin rows→Row} {amount : Fin rows→ℕ}
    (A₀ : CatalogueRows.Alignment (P).catalogue v.sampler π v.depth marks M word amount
      ((P).catalogue.original v.sampler π v.depth marks order (v.wideBoughtOrdinal h width π marks)))
    (m : Boot.Tape h D)
    (header : CoreCatalogue.Header order base v.wideJobs (CoreCatalogue.groupStart h v.W) M m)
    (core : CoreRoute.Seen order M groups directory (v.wideSources h width).2 v.depth π m)
    (packed : (RoleRoom.tables v.sampler order directory rows).Resident start m)
    (site : SiteROM.Resident directory ((z).offset start) m)
    (shelf : ∀e : Bought v.sampler π v.depth marks,
      ((published).shelf e.1).PortData v.sampler π v.depth (BoughtLocation.keyOf e.2) m)
    (rootFit : CoreCatalogue.top h v.W K G H R<2^w) (roleFit : (z).ceiling start<2^w)
    (rowFit : rows<2^w) (jobs : v.wideJobs≤2^w) (keyFit : PurchaseFrozen.count h D k≤2^w)
    (tileFit : (v.depth+1)*PurchaseFrozen.paths h v.sampler.degree v.depth≤2^w)
    (i : Fin rows) (live : 0<amount i) (s : Bool) :
    Resolved (h := h) (W := v.W) (k := k) (attempts := v.wideJobs) («w» := Native.wordBits h (2^v.W) Native.copies)
      v.sampler ((z).chart start) (v.widePaidPorts h width start s) m (i.val:Word w)
      (.inl (livePort v.sampler (P).catalogue π marks unique order (v.wideBoughtOrdinal h width π marks)
        A₀ i live s)) := by
  refine paid_selection (h := h) (W := v.W) (k := k) (attempts := v.wideJobs)
    («w» := Native.wordBits h (2^v.W) Native.copies) (depth := v.depth) (M := M)
    v.sampler ((z).chart start) (P).catalogue π marks unique order (v.wideBoughtOrdinal h width π marks)
    A₀ m (coreInputs base ((z).free start) R bits super K k v.wideJobs)
    (boughtInputs published v.sampler h v.W k v.depth K) rowFit ?_ ?_ i live s
  · intro a side
    have ns : 0<(permutationFabric h D).shapes.length := by rw [fixed_stage_count]; exact Nat.succ_pos _
    obtain ⟨ar,_,_,_,_,ptr,wide⟩:=CoreCatalogue.rooms_of_top ns rootFit
    have pubRoom : (z).publicRows≤(z).ceiling start := by
      simp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,
        RoleRoom.Sizes.axis,RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
      omega
    have heap : Native.heapEnd h D Native.copies≤CoreCatalogue.groupStart h v.W:=le_max_left ..
    have before : CoreCatalogue.groupStart h v.W≤ super:=Nat.le_add_right ..
    have one : (1:Word w)≠0 := by
      apply Fin.ne_of_val_ne
      have room := (Nat.succ_le_of_lt (Nat.two_pow_pos h)).trans_lt (v.date_prefix_fit h)
      simp [Nat.mod_eq_of_lt room]
    exact core_read v.sampler ((z).chart start) order base ((z).free start) bits super
      (CoreCatalogue.groupStart h v.W) M groups directory π v.depth marks unique m a side
      header core.board.columns.geometry core.board.columns.names ar (v.date_prefix_fit h).le wide one
      (heap.trans (before.trans ptr)) ptr rfl (pubRoom.trans roleFit.le) (packed.free side)
      packed.site packed.code rfl rfl site packed.positive core.board.columns.super
      core.board.columns.groupFit core.board.columns.siteFit
  · intro e side
    have one : (1:Word w)≠0 := by
      apply Fin.ne_of_val_ne
      have room := (Nat.succ_le_of_lt (Nat.two_pow_pos h)).trans_lt (v.date_prefix_fit h)
      simp [Nat.mod_eq_of_lt room]
    exact bought_read v.sampler ((z).chart start) published π v.depth marks unique groups groupNumber directory
      m e side (shelf e) (fun t=>(core.board.columns.geometry t).group) core.board.rom.names
      core.board.rom.outer core.board.rom.keys rfl rfl site packed.positive core.board.rom.tables
      jobs keyFit tileFit core.board.columns.groupFit core.board.columns.siteFit one

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
