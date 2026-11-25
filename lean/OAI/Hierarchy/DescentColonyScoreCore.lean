import OAI.Hierarchy.DescentColonyScanLeaves
import OAI.Hierarchy.DescentColonyLayout
import OAI.Hierarchy.DescentResidueMultiplication

namespace OAI
/-! # Computing the fixed-modulus score from finite marked site arrays -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBinaryField
open scoped BigOperators
variable {k : ℕ}

/-- Read the most significant coordinates first, with no basis search. -/
def integerAddress : (n : ℕ) → Bits n → ℕ
  | 0,_ => 0
  | n+1,x => 2*integerAddress n (headRows (Nat.le_succ n) x)+(x (Fin.last n)).val

private theorem integerAddress_value (n : ℕ) (x : Bits n) : integerAddress n x=value n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [integerAddress,value,ih]

/-- Convert binary output rows to their contiguous address in big-endian order. -/
def blockAddress (x : Bits k) : Block k := ⟨integerAddress k x,by
  rw [integerAddress_value]; exact (address k x).isLt⟩

theorem blockAddress_eq (x : Bits k) : blockAddress x=address k x := Fin.ext (integerAddress_value k x)

/-- Scan the input addresses for the unique preimage of the destination. This
uses forward residue multiplication and avoids computing scalar inverses. -/
def preimageWord (a μ : Bits k) (dest : Block k) : Option (Bits k) :=
  (words k).find? fun b => decide (blockAddress (multiply a μ b)=dest)

/-- The computed load at the permuted integer address. -/
def multiplierLoad {V : Type*} (weight : V→Block k→ℕ) (a μ : Bits k) (v : V) (dest : Block k) :=
  match preimageWord a μ dest with
  | none => 0
  | some b => weight v (blockAddress b)

variable {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G]

/-- The executable score for a given modulus and nonzero scalar. -/
noncomputable def uniformColonyScore (incoming : V → List V) (weight : G → V → Block k → ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) :=
  ∑g,Scan.leafScore incoming (multiplierLoad (weight g) a μ.val) D cap

end Hierarchy.DescentColonies

end OAI
