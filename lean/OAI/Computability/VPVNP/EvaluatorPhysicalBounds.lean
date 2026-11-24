import OAI.Computability.VPVNP.EvaluatorBinarySafety
import OAI.Computability.VPVNP.EvaluatorProgramInputBounds

/-!
# Literal tape clock and storage envelope of the evaluator

Compilation of the fixed stack bank costs quadratic time. Its simulated input
length is linear in the exponent width. The resulting exponent of the width
is a fixed four, independent of the advised matrices and their query times.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.BinaryMachine

open EvaluatorProgramMonomial EvaluatorProgramRawInput

/-- Physical clock sufficient for all stack instructions on the named bank. -/
def tapeTicks (rawLength ports stackTicks : ℕ) :=
  stackTicks*(6*(rawLength+(ports+1)+stackTicks)+4)

/-- A per-stack height bounds the packed bank, including its delimiter cells. -/
def packedCap (ports height : ℕ) := ports+1 + ports*height

/-- Two heads may move to either side of their initial position. -/
def headRadius (ports height : ℕ) := 7*packedCap ports height+4

/-- Uniform in the exponent width. All other parameters, including the two
coordinate-call clocks, admit the indicated singly exponential bound. -/
theorem tapeTicks_le_exp_poly (t Z ℓ Q A BF BM v w ports raw a : ℕ)
    (ha : A ≤ 2^a) (ht : t ≤ 2^a) (hℓ : ℓ ≤ 2^a) (hQ : Q ≤ 2^a)
    (hf : BF ≤ 2^a) (hm : BM ≤ 2^a) (hend : terminalTicks v w ≤ 2^a)
    (hp : ports+1 ≤ 2^a) (hr : raw ≤ A+(2*(t*Z)+6*Z+4)) :
    tapeTicks raw ports (fullTicks t Z ℓ Q A BF BM v w) ≤ 2^(6*a+23)*(Z+1)^4 := by
  let R := 2^(3*a+9)*(Z+1)^2
  let T := fullTicks t Z ℓ Q A BF BM v w
  have hR : 0 < R := Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (Nat.succ_pos _))
  have hz : 1 ≤ (Z+1)^2 := Nat.pow_pos (Nat.succ_pos _)
  have he : 2^a ≤ 2^(3*a+8)*(Z+1)^2 :=
    (Nat.pow_le_pow_right (by decide) (by omega : a ≤ 3*a+8)).trans (Nat.le_mul_of_pos_right _ hz)
  have htick : T ≤ R := fullTicks_le_exp_poly t Z ℓ Q A BF BM v w a 0 ha ht hℓ hQ
    (by simpa using hm) (by simpa using hf) (by unfold terminalTicks at hend; omega)
    (by unfold terminalTicks at hend; omega)
  have hE : 1 ≤ 2^a := Nat.two_pow_pos _
  have hEZ : Z ≤ 2^a*Z := by simpa using Nat.mul_le_mul_right Z hE
  have hTZ := Nat.mul_le_mul_right Z ht
  have hr' : raw ≤ 13*2^a*(Z+1) := by rw [Nat.mul_succ, Nat.mul_assoc]; omega
  have hr₁ : 13*2^a ≤ 2^(3*a+9) := calc
    _ ≤ 512*2^(3*a) := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right (by decide) (by omega))
    _ = _ := by rw [pow_add, Nat.mul_comm]; rfl
  have hraw : raw ≤ R := hr'.trans (Nat.mul_le_mul hr₁ (by nlinarith))
  have hports : ports+1 ≤ R := hp.trans (he.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))))
  have hmacro : 6*(raw+(ports+1)+T)+4 ≤ 32*R := by omega
  calc
    tapeTicks raw ports T ≤ R*(32*R) := Nat.mul_le_mul htick hmacro
    _ = 2^(6*a+23)*(Z+1)^4 := by
      unfold R
      rw [show 6*a+23 = ((3*a+9)+(3*a+9))+5 by omega, pow_add, pow_add]
      ring

/-- Uniform polynomial storage, including the head window of the literal
machine. All coordinate reader storage is accounted for in workspace. -/
theorem headRadius_le (t Z ℓ space A v w ports : ℕ) :
    headRadius ports (fullSpace t Z ℓ space A v w) ≤
      1110*(ports+1)*(t+Z+ℓ+space+A+v+w+1)^4 := by
  let n := t+Z+ℓ+space+A+v+w+1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hheight := fullSpace_le_power t Z ℓ space A v w
  change fullSpace t Z ℓ space A v w ≤ 157*n^4 at hheight
  have hp := Nat.mul_le_mul_left ports hheight
  have hnpos := Nat.pow_pos hn (n := 4)
  unfold headRadius packedCap
  change 7*(ports+1+ports*fullSpace t Z ℓ space A v w)+4 ≤ 1110*(ports+1)*n^4
  have hnports := Nat.le_mul_of_pos_right ports hnpos
  nlinarith

end Evaluator.BinaryMachine

end VPVNP
end Computability
end OAI
