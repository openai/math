import OAI.ThreeFlat.Diagonal.ProgramDirectoryData

namespace OAI
/-! # The terminal edge count determined by a physical program -/

namespace ThreeFlat.Diagonal.PhysicalStage.Program
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

/-- The terminal graph width table has a public number of rows even though every
row value and the successive base graphs depend on the selected histograms. -/
def finalEdges : {s : ℕ} → Program F s → ℕ → ℕ → ℕ
  | s,.done _,rem,v => v*2^s*2^rem
  | _,.shrink s _ _ _ tail,rem,v => tail.finalEdges rem (v*2^(CompressorPacking.tagBits (2^s)))
  | _,.refresh s _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail,rem,v => tail.finalEdges rem (v*2^s)

end
end ThreeFlat.Diagonal.PhysicalStage.Program

end OAI
