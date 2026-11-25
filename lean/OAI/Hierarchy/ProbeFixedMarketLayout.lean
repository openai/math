import OAI.Hierarchy.ProbeFixedMarketReady
import OAI.Hierarchy.ProtocolRAMCalendarStripBootSize

namespace OAI
/-! # The finite market pages loaded by the fixed chronological bootstrap -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StripDirectory PurchaseFrozen
open scoped Fin.CommRing Classical
private theorem layout_of_intervals {z d k jobs size : ℕ} (u v : Fin jobs → Market z d k)
    (original : Boot.Layout u size)
    (intervals : ∀ i, Boot.low (v i) = Boot.low (u i) ∧ Boot.high (v i) = Boot.high (u i))
    (threshold : ∀ i, (v i).shelf.table.base + (v i).shelf.table.size ≤ (v i).shelf.firstBase) :
    Boot.Layout v size := by
  refine ⟨original.subdivision, ?_, ?_, threshold, ?_⟩
  · intro i
    exact (original.afterHeap i).trans_eq (intervals i).1.symm
  · intro i
    exact (intervals i).2.le.trans (original.extent i)
  · intro i j x hi hj
    apply original.apart i j x
    · exact ⟨(intervals i).1.symm.le.trans hi.1, hi.2.trans_le (intervals i).2.le⟩
    · exact ⟨(intervals j).1.symm.le.trans hj.1, hj.2.trans_le (intervals j).2.le⟩

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "d" => (2^v.W)
local notation "A" => v.privateArena P z width
local notation "fmt" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "W" => wordBits z d copies
local notation "V" => Whole.markets v.mesh v.finish (v.basePhase width) fmt

set_option cleanup.letToHave false in
set_option maxHeartbeats 800000 in
private theorem market_flags_field (a : Attempt) :
    (fmt a).market.flags = Slab.flags (v.slab (v.seed P z width) P width)
      (v.sized (v.seed P z width) width) ((A).base v.mesh (.attempt a)) := by
  cases a <;> rfl

/-- All CT, threshold and immutable sampler pages of the priced reserve-rebased market
fit the originally loaded chronological table. -/
theorem market_layout (initial : heapEnd z d copies≤P.joint.initial) :
    Boot.Layout V ((A).endAddress v.mesh) := by
  let seed:=v.seed P z width
  let sized:=v.sized seed width
  let slab:=v.slab seed P width
  let old:=formats F v.mesh A P.joint.initial (Slab.install slab sized v.mesh)
  let U:=Whole.markets v.mesh v.finish (v.basePhase width) old
  have h : Boot.Layout U ((A).endAddress v.mesh):=
    Slab.boot_layout slab sized F v.mesh P.joint.initial v.finish (v.basePhase width)
      (initial.trans (v.market_initial_floor P z width))
  apply layout_of_intervals U V h
  · intro i
    let a := (Whole.attempts v.mesh)[i.val]
    have orig := Slab.sizes slab sized F v.mesh P.joint.initial a
    change (fmt a).market.shelf.thresholdBase = (old a).market.shelf.table.base ∧
      (fmt a).market.flags = (old a).market.flags
    exact ⟨(v.market_shelf_fields P z width a).1.trans orig.2.2.1.symm,
      (market_flags_field v P z width a).trans orig.2.2.2.2.1.symm⟩
  · intro i
    exact (v.market_inventory P z width ((Whole.attempts v.mesh)[i.val])).2

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
