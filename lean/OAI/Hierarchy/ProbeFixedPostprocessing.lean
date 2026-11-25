import OAI.Hierarchy.ProbeFixedPostWindows
import OAI.Hierarchy.ProbeFixedDiagnosticOriginal
import OAI.Hierarchy.ProbeFixedReserveInputs
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! # Native postprocessing on the original fixed paper chart and public link directory -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows BoughtSockets PurchaseStage
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (z width r K G H R idBase : ℕ) (joint : JointHeader.Board)
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
variable (origin : Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
local notation "s" => v.sampler
local notation "dir" => Public.join origin s z v.W k v.depth K G H R
local notation "cat" => liveBoard dir s z v.W k v.depth R K G H (CoreCatalogue.pointBits z v.W) idBase
local notation "P" => v.catalystPlacement z K G H R joint cat origin
local notation "A" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "W" => wordBits z (2^v.W) copies
local notation "coreEnd" => CoreRoute.stop s z v.W k n v.depth K G H R
variable (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "C" => v.nativeChart P z width r banks src tab dst owners

private theorem beforeLink {l : Link} {w cut : ℕ} (h : LinkOperands l w cut) : LinkInputs l cut :=
  ⟨PrefixAgreement.inputEnd_of_fits _ h.1,PrefixAgreement.inputEnd_of_fits _ h.2.1,
   PrefixAgreement.inputEnd_of_fits _ h.2.2.1,PrefixAgreement.inputEnd_of_fits _ h.2.2.2⟩

/-- All the register sources, including the radius and the endpoints of purchases, are
read from the actual indexed public data and coordinates of this calendar. -/
theorem native_snapshot (a : Attempt) (scheduled : Event.attempt a∈events v.mesh)
    (allocated : coreEnd≤joint.initial) (room : (A).endAddress v.mesh<2^W)
    (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W) :
    SnapshotReads ((C).layout a) (repair C a) (f a).board.keys := by
  let B:=repair C a
  let cut:=(f a).board.keys
  have key:=v.election_key_room z K G H R joint cat origin allocated
  have widthOk:=(v.post_window P z width a scheduled room).1
  obtain ⟨places,printed⟩:=v.stock_reader_extents P z width a key
  obtain ⟨stop,excess,payload,disc⟩:=v.post_policy_words P z width r banks src tab dst owners a threshold
  obtain ⟨regular,purchased,fee⟩:=v.original_links_at_keys z width r K G H R idBase joint origin
    banks src tab dst owners a allocated widthOk
  obtain ⟨decisions,saved,half,feed⟩:=v.stock_pass_inputs P z width r banks src tab dst owners a key
  exact ⟨places.1,decisions,stop,excess,payload,disc,beforeLink regular,beforeLink purchased,
    PrefixAgreement.inputEnd_of_fits _ fee,printed,places.2.1,saved,half,feed⟩

/-- Every physical postprocessing premise of the real single-program calendar follows
from address space and fixed integer size. No assumption is made on the selector words. -/
theorem fixed_post (a : Attempt) (scheduled : Event.attempt a∈events v.mesh)
    (allocated : coreEnd≤joint.initial) (room : (A).endAddress v.mesh<2^W)
    (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W) (widthWord : width<2^W)
    (alphabet : v.menu.alphabet≤2^W) (counters : v.menu.alphabet*width<2^W) :
    let B:=repair C a
    let L:=(C).layout a
    Board L B W ∧ (repairMask B).Fits W B.repairBits.base ∧ B.repairBits.base+L.candidates<2^W ∧
    (∀m : Memory W,AuditReady (audits L B) m) ∧ OrderedTallies (audits L B) ∧
      (verdict (audits L B)).Fits W B.verdict ∧ B.verdict+1<2^W := by
  intro B L
  have reads:=v.native_snapshot z width r K G H R idBase joint origin banks src tab dst owners
    a scheduled allocated room threshold
  have h:=v.post_audit_of_reads P z width r banks src tab dst owners a scheduled room
    widthWord alphabet counters reads
  have mask:=v.post_mask P z width r banks src tab dst owners a scheduled room threshold
  exact ⟨h.1,mask.1,mask.2,h.2.1,h.2.2.1,h.2.2.2,(v.post_window P z width a scheduled room).2⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
