import OAI.Computability.NearSquareRoot.InterchangeOpcodeTypes

/-! # Flat storage of chart words and rectangular incidences -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatAtlas

open Opcode

def labelIdx (m L : ℕ) (s : Bool) (j v : ℕ) := (s.toNat * m + j) * L + v

def commonIdx (m L T j t : ℕ) := 2 * m * L + j * T + t

def prepareIdx (m L T : ℕ) (s : Bool) (v t : ℕ) :=
  2 * m * L + m * T + (s.toNat * L + v) * T + t

def localIdx (m L T : ℕ) (s : Bool) (j v t : ℕ) :=
  2 * m * L + m * T + 2 * L * T + ((s.toNat * m + j) * L + v) * T + t

def maskIdx (L T : ℕ) (s : Bool) (t v : ℕ) := (s.toNat * T + t) * L + v

def chart (A : List Word) (i : ℕ) := A.getD i []

def mask (bits : List Bool) (L T : ℕ) (s : Bool) (t v : ℕ) :=
  bits.getD (maskIdx L T s t v) false

end FlatAtlas

end NearSquareRoot
end Computability
end OAI
