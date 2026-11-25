import OAI.Optimization.LinearProgramming.Lattice.BitState
import OAI.Optimization.LinearProgramming.Lattice.BitList

/-! Input-sized table construction and binary indexed access for the packed LLL state. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

variable {C A D : Type} {ec : C → List Bool} {ea : A → List Bool} {ed : D → List Bool}

noncomputable def getAtP {xs : C → List A} {i : C → ℕ} (d : A)
    (rows : Procedure ec (listCode ea) xs) (idx : Procedure ec Nat.bits i) :
    Procedure ec ea (fun c => readAt d (xs c) (i c)) :=
  (listGet ea d).comp (idx.pair rows)

noncomputable def tableRowP {A : C → IntMatrix} {i : C → ℕ}
    (rows : Procedure ec intMatrixCode A) (idx : Procedure ec Nat.bits i) :
    Procedure ec intRowCode (fun c => rowAt (A c) (i c)) := getAtP [] rows idx

noncomputable def tableEntryP {A : C → IntMatrix} {i j : C → ℕ}
    (rows : Procedure ec intMatrixCode A) (ip : Procedure ec Nat.bits i)
    (jp : Procedure ec Nat.bits j) : Procedure ec intCode (fun c => entryAt (A c) (i c) (j c)) :=
  getAtP 0 (tableRowP rows ip) jp

noncomputable def natEqP {a b : C → ℕ} (x : Procedure ec Nat.bits a)
    (y : Procedure ec Nat.bits b) : Procedure ec boolCode (fun c => decide (a c = b c)) :=
  PriceGame.Control.Native.natEqP.comp (x.pair y)

noncomputable def succIndexP {i : C → ℕ} (p : Procedure ec Nat.bits i) :
    Procedure ec Nat.bits (fun c => i c + 1) := binaryAdd.comp (p.pair (constant ec Nat.bits 1))

noncomputable def predIndexP {i : C → ℕ} (p : Procedure ec Nat.bits i) :
    Procedure ec Nat.bits (fun c => i c - 1) := binarySub.comp (p.pair (constant ec Nat.bits 1))

/-- Tabulate against an actual input frame. Even a binary selector that lies beyond
the last row cannot extend this loop past the number of serialized entries. -/
noncomputable def tabulateBinaryAlongP {xs : C → List A} {cell : C → ℕ → D} (da : A) (dd : D)
    (source : Procedure ec (listCode ea) xs)
    (body : Procedure (prodCode Nat.bits ec) ed (fun x => cell x.2 x.1)) :
    Procedure ec (listCode ed) (fun c => (List.range (xs c).length).map (cell c)) := by
  let index := unaryToBits.comp (first unaryCode ec)
  let ctx := second unaryCode ec
  exact tabulateAlongP da dd source (body.comp (index.pair ctx))

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
