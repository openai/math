import OAI.Hierarchy.ProbeFixedCatalystPurchasedLocal
import OAI.Hierarchy.ProbeFixedBirthFees
import OAI.Hierarchy.ProbeFixedQuietAttemptStock

namespace OAI
/-! # A committed reserve row certifies the actual outer purchase and its public marks -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart CatalystArchive
open BoughtSockets PurchaseStage StockBound StockCommit PurchaseFrozen StripDirectory
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) {K H R : ℕ} (z width : ℕ)
  (b : JointHeader.Board) (cat : CatalogueRows.Board)
set_option quotPrecheck false
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "N" => Stages z (2^v.W)
local notation "w" => wordBits z (2^v.W) copies
variable (groups : Fin K≃AllGroups z (2^v.W))
  (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z v.W (ReportSockets.copies k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))) H)
  (socket : BoughtSockets.Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)) (r : ℕ) (banks : RouteSettlement.Banks)
  (src tab dst : ℕ) (owners : Bank)
local notation "P" => v.catalystPlacement z K dir.groups H R b cat socket
local notation "s" => v.nativeBoards P z width
local notation "A" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "forms" => v.nativeFormats P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "incoming" => resolvedStock v.mesh A b.initial (build F s)
local notation "core" => CoreRoute.stop v.sampler z v.W k n v.depth K dir.groups H R


variable (initial : Memory (wordBits z (2^v.W) copies)) (π : Equiv.Perm (Fin (2^z)))
    (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice : Fin v.mesh.reserveSteps) (inner : Fin v.mesh.innerFuel)
local notation "ev" => Attempt.inner phase.val trial.val slice.val inner.val
local notation "before" => entryMemory C initial ev
local notation "mkt" => v.frozenMarket P z width phase.val trial.val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
omit [Nonempty (Fin k)] in
theorem committed_parent_mode (whole : Calendar.mounted C (events v.mesh) initial)
    (archive : ArchiveRoom C initial (v.mesh.inject+v.mesh.cool))
    (layout : TrialLayout C ev (forms ev).pricedArea (forms ev).stockSource (g ev) v.keepLimit width
      ((A).base v.mesh (.attempt ev)))
    (live : ∃j,j∈liveRows (v.ballot P z width r banks src tab dst owners ev)
      (v.stage P z width r banks src tab dst owners ev before) (forms ev).market.rows) :
    observedMode C initial phase.val trial.val=3 := by
  obtain ⟨rest,cut⟩:=inner_slot C initial phase.val trial.val slice.val inner.val
    phase.isLt trial.isLt slice.isLt inner.isLt whole
  obtain ⟨j,hit⟩:=live
  have atEntry:=cut.entryMemory
  have ready : Calendar.ready C (.attempt ev) before := atEntry.symm ▸ cut.currentReady
  have two : seen C ev before=2 := by
    by_contra quiet
    exact v.rows_off_of_ne P z width r banks src tab dst owners ev before ready layout quiet j
      (Finset.mem_filter.mp hit).2
  have actual : observedHistory C initial ev=2 := by
    change seen C ev (innerState C initial phase.val trial.val slice.val inner.val)=2
    rw [←atEntry]; exact two
  by_contra didNotBuy
  have off : disabled v.mesh (observedHistory C initial) ev:=Or.inl didNotBuy
  have law:=archive.inner_law phase.val trial.val slice.val phase.isLt trial.isLt slice.isLt inner.val inner.isLt
  change (if disabled v.mesh (observedHistory C initial) ev then observedHistory C initial ev=0 else _) at law
  rw [ite_eq_left off] at law
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2500000 in
/-- Compare the receipt used by the dated stock packet to the original
public catalogue. This statement uses the actual compiled birth at the
canonical rank and remains valid when every row in the packet is quiet. -/
theorem committed_birth_marks (whole : Calendar.mounted C (events v.mesh) initial)
    (archive : ArchiveRoom C initial (v.mesh.inject+v.mesh.cool))
    (late : v.stripHeight≤z) (payload : width≤2^z) (heap : heapEnd z (2^v.W) copies≤b.initial)
    (coreEnd : core≤b.initial)
    (board : DatedBoard F s v.mesh cat (P).routes π groups dir (.outer phase trial) (entryMemory C initial (.outer phase trial)))
    (calibrated : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤z)
    (layout : TrialLayout C ev (forms ev).pricedArea (forms ev).stockSource (g ev) v.keepLimit width ((A).base v.mesh (.attempt ev))) :
    let localData:=v.purchasedLocal (R:=R) z width b cat groups dir socket r banks src tab dst owners initial π
      phase trial slice inner whole late payload heap coreEnd board calibrated layout
    (∃j,j∈liveRows (v.ballot P z width r banks src tab dst owners ev)
      (v.stage P z width r banks src tab dst owners ev before) (forms ev).market.rows) →
      v.birthMarks P z width r banks src tab dst owners initial (finProdFinEquiv (phase,trial))=
      StripDirectory.actualMarks ({((s).outer phase.val trial.val).market.shelf with stockBase:=localData.receipt.stock} : Shelf)
        localData.receipt.phase localData.receipt.price localData.receipt.kind localData.receipt.frozen (k:=k) := by
  intro localData live
  have mode:=v.committed_parent_mode (R:=R) z width b cat dir socket r banks src tab dst owners initial
    phase trial slice inner whole archive layout live
  simp only [birthMarks,outerDates,Equiv.symm_apply_apply]
  rw [Shelf.catalogueMarks_buy _ _ _ _ _ _ mode]
  rfl


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
