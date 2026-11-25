import OAI.ThreeFlat.Diagonal.HalfMemory
import OAI.ThreeFlat.Diagonal.AuxiliaryPath

namespace OAI
/-! # Fixings and exact matrix of one block

The bit strings in a fixing are the old and new values of each visited
chunk, the initial auxiliary word, and each successive auxiliary word.
Consistent auxiliary paths are represented exactly once.
-/

namespace ThreeFlat.Diagonal

abbrev BlockFixing (n : ℕ) (S A : Type*) := (Fin n → S) × (Fin n → S) × A × (Fin n → A)

variable {F S A I : Type*} [Field F] [Fintype S] [DecidableEq S] [Inhabited S]
  [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I] {n : ℕ}

/-- The four strings at one tick constitute its local pin data. -/
def fixingWeight (tick : Fin n → S → S → Matrix A A F) (f : BlockFixing n S A) : F :=
  auxProduct n (fun i => tick i (f.1 i) (f.2.1 i)) f.2.2.1 f.2.2.2

/-- The matrix for a fixing with its specified initial and final values.
The catalyst argument can be either a scalar identity or an approximate entry. -/
noncomputable def physicalFixing (atSlot : Fin n → I) (active : Bool)
    (f : BlockFixing n S A) (M : Matrix (I → S) (I → S) F) :
    Matrix (MachineState I S A) (MachineState I S A) F :=
  fixingMatrix (halfCoordinates atSlot active) (halfCoordinates atSlot active)
    (checkEnd (f.1, f.2.2.1)) (checkEnd (f.2.1, endWord n f.2.2.1 f.2.2.2)) M

end ThreeFlat.Diagonal

end OAI
