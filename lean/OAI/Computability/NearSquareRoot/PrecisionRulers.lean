import OAI.Computability.IntegerMultiplication.Code.Padding

/-! # Affine changes of a unary width ruler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication IntegerMultiplication.Code

def affineTally (a b : ℕ) (l : Tally) : Tally :=
  (l.map fun _ => tally a).flatten ++ tally b

theorem easyAffine (a b : ℕ) : Easy (affineTally a b) := by
  unfold affineTally
  fun_prop

theorem affine_tally (a b k : ℕ) : affineTally a b (tally k) = tally (a*k+b) := by
  simp [affineTally, tally, Nat.mul_comm]

end NearSquareRoot
end Computability
end OAI
