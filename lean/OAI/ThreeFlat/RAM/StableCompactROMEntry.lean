import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Three-word public records for stable-compaction source operands -/

namespace ThreeFlat.RAM.StableCompactROMProgram

inductive Entry where
  | literal (value : ℕ)
  | siteBit (bit : ℕ)
  | pin (stream : Fin 3)
  | hidden (reg mask : ℕ)

def Entry.kind : Entry → ℕ
  | .literal _ => 0
  | .siteBit _ => 1
  | .pin _ => 2
  | .hidden _ _ => 3

def Entry.payload : Entry → ℕ
  | .literal value => value
  | .siteBit bit => bit
  | .pin stream => stream.val
  | .hidden reg _ => reg

def Entry.mask : Entry → ℕ
  | .hidden _ mask => mask
  | _ => 0

def Entry.word (e : Entry) : Fin 3 → ℕ := ![e.kind,e.payload,e.mask]

def Entry.Fits (e : Entry) (w : ℕ) : Prop :=
  match e with
  | .siteBit bit => bit < 2^w
  | .hidden _ mask => mask < 2^w
  | _ => True

/-- The same address layout covers an empty cropped bank and parallel wires. -/
def Entry.atSite (e : Entry) (N n v : ℕ) : ℕ :=
  match e with
  | .literal value => value
  | .siteBit bit => (v.testBit bit).toNat
  | .pin stream => if v < n then 2 + stream.val*n + v else 0
  | .hidden reg mask => 2 + 3*n + reg*N + (v ^^^ mask)

end ThreeFlat.RAM.StableCompactROMProgram

end OAI
