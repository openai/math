import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasTypes
import OAI.Computability.NearSquareRoot.InterchangeOpcodeCodec
import OAI.Computability.NearSquareRoot.InterchangeOpcodeCompute

/-! # Numerical tests for the stored rectangle diagrams -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatAtlas

open Opcode

def allN (k : ℕ) (f : ℕ → Bool) := (List.range k).all f

def sides (f : Bool → Bool) := f false && f true

def shape (b a m : ℕ) (A : List Word) (limit i : ℕ) :=
  admissible b (a+m+a) (chart A i) && decide (price (chart A i) ≤ limit)

def edge (a m L T : ℕ) (A : List Word) (s : Bool) (j v t : ℕ) :=
  equal (a+m+a) (chart A (prepareIdx m L T s v t) ++ chart A (localIdx m L T s j v t) ++
    chart A (commonIdx m L T j t)) (chart A (labelIdx m L s j v))

def pivot (i : ℕ) : Op := (2,(false,i),(true,i),false,0,1)

def diag (a m L : ℕ) (A : List Word) (j v : ℕ) :=
  equal (a+m+a) (pivot (a+j) :: chart A (labelIdx m L true j v)) (chart A (labelIdx m L false j v))

def valid (b a m L T : ℕ) (bits : List Bool) (A : List Word) :=
  sides (fun s => allN m fun j => allN L fun v => shape b a m A (54*(a+2)) (labelIdx m L s j v)) &&
  allN m (fun j => allN T fun t => shape b a m A (54*(a+2)) (commonIdx m L T j t)) &&
  sides (fun s => allN L fun v => allN T fun t =>
    !mask bits L T s t v || shape b a m A (54*(a+2)) (prepareIdx m L T s v t)) &&
  sides (fun s => allN m fun j => allN L fun v => allN T fun t =>
    !mask bits L T s t v || (shape b a m A 0 (localIdx m L T s j v t) && edge a m L T A s j v t)) &&
  allN m (fun j => allN L fun v => diag a m L A j v)

end FlatAtlas

end NearSquareRoot
end Computability
end OAI
