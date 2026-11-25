import OAI.ThreeFlat.Diagonal.TraceRowCode

namespace OAI
/-! # Canonical binary coordinates for all CPU row guesses -/

namespace ThreeFlat.Diagonal.TraceRows

open Computability.VPVNP BurstRAM RAMSerialization TraceBanks
variable {w p r : ℕ}

/-- CPU representation is a collection of separate consecutive row codes. -/
abbrev CpuBits (w r f : ℕ) := Fin f → Fin ((5+r)*(w+1)) → Bool

def writeCpu {f : ℕ} (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (xs : Fin f → Row (w+1) (Snapshot w p r)) :
    CpuBits w r f := fun i => (rowFormat hw hp).encode (xs i)

def readCpu {f : ℕ} (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (xs : CpuBits w r f) :
    Fin f → Row (w+1) (Snapshot w p r) :=
  fun i => (rowFormat hw hp).parse ((arrayBits (5+r) (w+1)).symm (xs i))

@[simp] theorem read_write_cpu {f : ℕ} (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (xs : Fin f → Row (w+1) (Snapshot w p r)) :
    readCpu hw hp (writeCpu hw hp xs) = xs := by
  funext i
  simp [readCpu, writeCpu, Format.encode, Format.parse_words]

end ThreeFlat.Diagonal.TraceRows

end OAI
