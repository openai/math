import OAI.Computability.VPVNP.CompressorShrinkHistoryDirectory
import OAI.Computability.VPVNP.CompressorRefreshTraversalHeaders
import OAI.Computability.VPVNP.CompressorSlotWidthState
import OAI.Computability.VPVNP.CompressorRecordsDemandOutput

/-! # Physical incidence pointers after the shrinking substep header

The old level retains its pointer bank. The successor publisher uses precisely
the number of lane slots traversed by the shrinking construction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkGeometryHeadBanks

open BurstRAM Compression DescriptorSpace BlockHeaderRun ShrinkSlots
open PortRefresh.TraversalHeaders PairSimulation.TraversalRows

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps) {g w : ℕ}
variable (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
variable (sel : SelectedScore.Selection B X) (bits : List Bool)

local notation "lv" => shrinkLevel B f hf i X sel bits
local notation "sh" => levelShape (b := S.degreeExponent i.succ) X

theorem output_slots : (lv).outputSlots = actualCount sh := by
  let Y := X.shrinkNext B.shrink (S.shrink i) sel
  change Y.positions * 2^S.degreeExponent i.succ = _
  rw [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv g),Fintype.card_fin]
  exact (next_counts X B.shrink (S.shrink i) sel).2

/-- The actual scalar and pointer publishers install both banks in the same
memory, with the compact lengths required by the slot and incidence workers. -/
theorem after_substep {L : Layout} {old new : Fin L.levels} {six : 6 ≤ L.shape.scalarFields} {m : Memory w}
    (sub : Substep lv L old new six m) (later : old.val < new.val)
    (heads : HeadBank L old (DemandRAM.oldCount X) m) :
    HeadBank L old (DemandRAM.oldCount X) (finalMemory lv L old new m) ∧
    HeadBank L new (actualCount sh) (finalMemory lv L old new m) := by
  obtain ⟨oldHeads,newHeads⟩ := headBanks_of_substep sub later heads
  exact ⟨oldHeads,(output_slots B f hf i X sel bits) ▸ newHeads⟩

end CompressorRecords.ShrinkGeometryHeadBanks

end VPVNP
end Computability
end OAI
