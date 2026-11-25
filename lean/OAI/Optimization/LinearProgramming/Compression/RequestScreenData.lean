import OAI.Optimization.LinearProgramming.Compression.Request

/-! Scalar specification for inspecting packed rational rows. The deployment theorem
compares this reference directly with the register and bit-program implementations. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable
namespace ScreenData

/-- Squared length of a packed rational graph row. -/
def rowSquare (row : List ℚ) : ℚ := (row.map (fun q => q*q)).sum

/-- The coefficient immediately preceding the last graph coordinate must be nonzero. -/
def rowPass (d : ℕ) (row : List ℚ) : Bool :=
  decide (((row.drop (d-1)).headD 0).num ≠ 0 ∧ rowSquare row ≤ (requestCutoff d : ℚ)^2)

/-- The first accepting original index, with the row count as failure sentinel. -/
def screenRows (rows : List (List ℚ)) : ℕ :=
  (rows.map (fun row => if rowPass rows.length row then (1 : ℕ) else 0)).idxOf 1

end ScreenData
end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
