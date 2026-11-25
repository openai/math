import OAI.Hierarchy.ProbeFixedNativeBoards

namespace OAI
/-! # Sampler addresses on the mounted payload and purchase boards -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen StripChart
open scoped Classical

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)

set_option cleanup.letToHave false in
set_option maxHeartbeats 800000 in
/-- Both native attempt formats use the allocated sampler table and its original degree. -/
theorem market_shelf_fields (a : Attempt) :
    let seed := v.seed P z width
    let sized := v.sized seed width
    let slab := v.slab seed P width
    let base := (v.privateArena P z width).base v.mesh (.attempt a)
    let m := (v.nativeFormats P z width a).atTime v.mesh v.finish (v.basePhase width) a
    m.shelf.thresholdBase = base + Slab.selectorSpan sized + Slab.failureSpan sized ∧
      m.shelf.table.size = 2^(z + slab.thresholdExtra) ∧
      m.shelf.firstBase = Slab.first slab sized base ∧
      m.sampler.degree = v.sampler.degree := by
  intro seed sized slab base m
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases a <;> rfl
  · cases a <;> rfl
  · cases a <;> rfl
  · cases a <;> rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
