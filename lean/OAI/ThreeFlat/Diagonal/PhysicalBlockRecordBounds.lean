import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule
import OAI.ThreeFlat.Diagonal.PhysicalRecordAlphabet
import OAI.ThreeFlat.Diagonal.PhysicalShrinkCopies

namespace OAI
/-! # Public alphabet and copy bounds for the repeated physical program -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open CompressorPacking
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (B : Block F)

def shrinkRecordBounds : ℕ → ℕ → List (ℕ×ℕ)
  | 0,_ => []
  | n+1,i => (shrinkSymbolBound B.shrink,
      shrinkCopyFactor (2*2^(B.exponent i)+1) (2^(B.exponent i))) :: shrinkRecordBounds n (i+1)

def fixedRecordBounds : List (ℕ×ℕ) :=
  B.shrinkRecordBounds B.levels 0 ++ [(refreshSymbolBound B.refresh,1+2*(2^(B.exponent B.levels))*(2^(B.exponent B.levels)))]

def alphabetCap := (B.fixedRecordBounds.map Prod.fst).sum

def repeatFactor := (B.fixedRecordBounds.map Prod.snd).sum

end
end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
