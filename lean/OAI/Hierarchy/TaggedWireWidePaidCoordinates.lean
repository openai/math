import OAI.Hierarchy.TaggedWireWideSocketDirectory
import OAI.Hierarchy.ProtocolRAMCoreRouteImage
import OAI.Hierarchy.ProtocolRAMCoreCatalogueSpace
import OAI.Hierarchy.ProbePublicStageCount
import OAI.Hierarchy.TaggedWireAlignedSlots

namespace OAI
/-! # Numerical group and slot addresses in the original wide paid directory -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open CatalogueRows
open BoughtSockets CoreRoute PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
variable (h width : ℕ)
set_option quotPrecheck false
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies
local notation "P" => v.widePlacement h width
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "G" => (directory).groups
local notation "rows" => (P).catalogue.rows
local notation "z" => RoleRoom.shape («R»:=R) v.sampler directory rows
local notation "base" => CoreCatalogue.headBase h v.W K G H
local notation "super" => CoreCatalogue.superStart h v.W
local notation "bits" => CoreCatalogue.pointBits h v.W
local notation "published" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K G H R

local notation "order" => v.wideOrder h width
local notation "groups" => WideMemory.groups h v.W

variable (start M : ℕ) (π : Equiv.Perm (Fin (2^h))) (marks : Marks h v.W k v.wideJobs)
  (unique : Exclusive marks)

/-- The fixed socket descriptor reads the original CT, permutation and group name.
Its two coordinates use the original supergroup header in the same memory. -/
theorem wide_core_coordinates (m : Boot.Tape h D)
    (header : CoreCatalogue.Header order base v.wideJobs (CoreCatalogue.groupStart h v.W) M m)
    (core : CoreRoute.Seen order M groups directory (v.wideSources h width).2 v.depth π m)
    (rootFit : CoreCatalogue.top h v.W K G H R<2^w)
    (t : StageAt h D) (p : Fin (2^h)) (l : ColumnLayer k) (side : Bool) :
    Coordinates directory (coreInputs base ((z).free start) R bits super K k v.wideJobs side) m
      ((((order).symm (.inr ((p,t),l))).val):Word w)
      (locate v.sampler π v.depth marks unique (.inl ((t,p),l),side)) := by
  have ns : 0<(permutationFabric h D).shapes.length := by rw [fixed_stage_count];exact Nat.succ_pos _
  obtain ⟨ar,_,_,_,_,ptr,wide⟩:=CoreCatalogue.rooms_of_top ns rootFit
  have old : Native.heapEnd h D Native.copies≤CoreCatalogue.groupStart h v.W:=le_max_left ..
  have lower : CoreCatalogue.groupStart h v.W≤ super:=Nat.le_add_right ..
  have tiles : 2^h≤2^w := Nat.pow_le_pow_right (by decide) (by rw [Native.wordBits_linear]; omega)
  exact core_coordinates v.sampler order base ((z).free start) bits super (CoreCatalogue.groupStart h v.W)
    M groups directory π v.depth marks unique m _ t p l side ((order).apply_symm_apply _) header
    core.board.columns.geometry core.board.columns.names ar tiles wide
    (old.trans (lower.trans ptr)) ptr core.board.columns.super

/-- The acquired endpoint uses the dated birth shelf's literal source tile, its
native ordinal and the same immutable group directory. -/
theorem wide_bought_coordinates (m : Boot.Tape h D)
    (core : CoreRoute.Seen order M groups directory (v.wideSources h width).2 v.depth π m)
    (shelf : ∀e : Bought v.sampler π v.depth marks,
      ((published).shelf e.1).PortData v.sampler π v.depth (BoughtLocation.keyOf e.2) m)
    (jobs : v.wideJobs≤2^w) (keyFit : PurchaseFrozen.count h D k≤2^w)
    (tileFit : (v.depth+1)*PurchaseFrozen.paths h v.sampler.degree v.depth≤2^w)
    (e : Bought v.sampler π v.depth marks) (side : Bool) :
    Coordinates directory (boughtInputs published v.sampler h v.W k v.depth K side) m
      ((v.wideBoughtOrdinal h width π marks e).val:Word w)
      (locate v.sampler π v.depth marks unique (.inr e,side)) :=
  bought_coordinates v.sampler published π v.depth marks unique groups groupNumber directory m e side
    (shelf e) (fun t=>(core.board.columns.geometry t).group) core.board.rom.names
    core.board.rom.outer core.board.rom.keys core.board.columns.super jobs keyFit tileFit

/-- An original paid report row selects the two physical words of precisely
its labelled socket, on either side and in either catalogue interval. -/
theorem wide_paid_coordinates (m : Boot.Tape h D)
    (header : CoreCatalogue.Header order base v.wideJobs (CoreCatalogue.groupStart h v.W) M m)
    (core : CoreRoute.Seen order M groups directory (v.wideSources h width).2 v.depth π m)
    (shelf : ∀e : Bought v.sampler π v.depth marks,
      ((published).shelf e.1).PortData v.sampler π v.depth (BoughtLocation.keyOf e.2) m)
    (rootFit : CoreCatalogue.top h v.W K G H R<2^w) (rowFit : rows<2^w)
    (jobs : v.wideJobs≤2^w) (keyFit : PurchaseFrozen.count h D k≤2^w)
    (tileFit : (v.depth+1)*PurchaseFrozen.paths h v.sampler.degree v.depth≤2^w)
    (r : ReportSockets.Row v.sampler π v.depth marks) (side : Bool) :
    let ord:=(P).catalogue.original v.sampler π v.depth marks order (v.wideBoughtOrdinal h width π marks)
    Coordinates directory (v.widePaidPorts h width start side) m
      ((ord ((HistoryRoles.labelled v.sampler π v.depth marks).symm (.inr r))).val:Word w)
      (locate v.sampler π v.depth marks unique (r,side)) := by
  intro ord
  exact CatalogueRows.Alignment.table_coordinates (S:=v.sampler) (π:=π) (depth:=v.depth) (marked:=marks)
    (unique:=unique) (b:=(P).catalogue) («order»:=order) (acquired:=v.wideBoughtOrdinal h width π marks) (dir:=directory)
    m (coreInputs base ((z).free start) R bits super K k v.wideJobs)
    (boughtInputs published v.sampler h v.W k v.depth K) rowFit
    (v.wide_core_coordinates h width start M π marks unique m header core rootFit)
    (v.wide_bought_coordinates h width M π marks unique m core shelf jobs keyFit tileFit) r side

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
