import OAI.ThreeFlat.Diagonal.CompressorOutputCaps
import OAI.ThreeFlat.Diagonal.ShrinkRowScan

namespace OAI
/-! # Fixed word bounds for the native shrinking tables -/
namespace Hierarchy.TraceShrinkRetained

open ThreeFlat Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.Compression CompressorPacking Native Native.ShrinkStage Resident
open NavigationPass ShrinkStageNav
noncomputable section
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D : ℕ)
set_option quotPrecheck false
local notation "d" => (2^s : ℕ)
local notation "k" => (2*d+1 : ℕ)
local notation "S" => shrinkStage s D
local notation "t" => tagBits d

/-- Constants in the shrink program, independent of the run and its histogram. -/
def fixedWords : ℕ :=
  80 + d + 2^k + 2^t + (3*(2^k*d)/4) + D + (S).pieceRadix + keyBound S 1 t +
    T.more.length+1 + widthMultiplicity k d + shrinkBaseBound T + shrinkMotifWidthFactor T k d


end
end Hierarchy.TraceShrinkRetained

end OAI
