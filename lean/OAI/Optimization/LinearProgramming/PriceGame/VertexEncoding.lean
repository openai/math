import OAI.Optimization.LinearProgramming.PriceGame.StatesMass
import Mathlib.Logic.Equiv.Fin.Basic

/-! Executable array addresses for the duplicated coordinates of a recursive trial. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace States
namespace Mass

/-- Encode nested coordinate pairs using mixed-radix indexing. Both maps are executable;
the code constructs the equivalence recursively and needs no choice of enumeration. -/
def vertexEquivFin (n : ℕ) : (k : ℕ) → Vertex n k ≃ Fin (n * 2^k)
  | 0 => finCongr (by simp)
  | k + 1 =>
    ((vertexEquivFin n k).prodCongr finTwoEquiv.symm).trans
      (finProdFinEquiv.trans (finCongr (by rw [pow_succ, Nat.mul_assoc])))

/-- Array decoding recovers exactly the requested vertex, at every depth. -/
theorem decode_encode (n k : ℕ) (v : Vertex n k) :
    (vertexEquivFin n k).symm ((vertexEquivFin n k) v) = v :=
  (vertexEquivFin n k).symm_apply_apply _

/-- Every array address is used. -/
theorem encode_decode (n k : ℕ) (j : Fin (n*2^k)) :
    (vertexEquivFin n k) ((vertexEquivFin n k).symm j) = j :=
  (vertexEquivFin n k).apply_symm_apply _

end Mass
end States
end PriceGame
end LinearProgramming
end Optimization
end OAI
