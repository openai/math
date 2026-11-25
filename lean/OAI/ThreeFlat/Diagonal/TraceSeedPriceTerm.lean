import Mathlib.Data.Nat.Basic

namespace OAI
/-! # The directory's physical charge for one native cursor seed -/

namespace ThreeFlat.Diagonal.TraceBitHeader
/-- Physical resources billed by the directory at cursor stage zero. -/
def seedTraceWork (low stride cells copies depth : ℕ) :=
  1+2^low*(2*stride+cells+12*(copies+1)*(1+(depth+depth))*cells)

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
