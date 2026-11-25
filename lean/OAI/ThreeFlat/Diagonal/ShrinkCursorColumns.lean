import OAI.ThreeFlat.Diagonal.ShrinkRecordBase
import OAI.ThreeFlat.Diagonal.PhysicalShrinkBase
import OAI.ThreeFlat.Diagonal.ShrinkNavigationLocal
import OAI.ThreeFlat.Diagonal.ShrinkCursorLayout
import OAI.ThreeFlat.Diagonal.RefreshCursorLayout

namespace OAI
/-! # True graph and width columns between successive native stage calls -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking Native Native.ShrinkStage Native.ShrinkStage.Resident
open NavigationDirectory NavigationPass PhysicalShrink
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
set_option quotPrecheck false
local notation "d" => (2^s:ℕ)
local notation "t" => tagBits d
local notation "S" => shrinkStage s D
local notation "M" => shrinkBinary T s D rem hD small A
local notation "Q" => shrinkBinaryFamily T s D rem hD small A
local notation "N" => Fintype.card (shrinkRecordState s rem A).Base
local notation "x" => dims S N t rem

theorem shrink_input_columns (K : ℕ) (c : Cursor) :
    incoming S N (pointers K c x)=RefreshStageNav.oldColumns c (Fintype.card A.Base) d := by
  change (⟨c.graph,N*d,c.width⟩ : SlotImage.Columns)=_
  rw [shrink_record_base s rem A]; rfl

theorem shrink_output_columns (K : ℕ) (c : Cursor) (branch : Fin (M).rules.count) :
    outgoing S N t (pointers K c x)=RefreshStageNav.oldColumns (allocate K c (.shrink x)).next
      (Fintype.card ((M).next branch).Base) D := by
  rw [shrinkBinary_next_base T s D rem hD small A branch,←shrink_record_base s rem A]; rfl


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
