import OAI.Optimization.LinearProgramming.RAM.CallableTwoBoot
import OAI.Optimization.LinearProgramming.RAM.FrameFirstHeader

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

open Call Tape

/-- The compiler evaluates the register-address and time envelope as ordinary natural
address arithmetic. It reads the two input dimensions and uses no input scalar value. -/
def lpTimeFloor (registerBound C E : ℕ) : AddressTerm 2 :=
  let n : AddressTerm 2 := .reg 0+.reg 1
  .val registerBound+2*n+3+.val C * addressPower (n+1) E

@[simp] theorem lpTimeFloor_value (registerBound C E m d : ℕ) :
    (lpTimeFloor registerBound C E).value (dimensions m d) =
      registerBound+2*(m+d)+3+polyBound C E (m+d) := by
  simp [lpTimeFloor,AddressTerm.value,AddressOp.value,dimensions,polyBound]

/-- `cap` accounts for the complete time bound and encoded input addresses, including
the final native decision instructions. -/
theorem lpTimeFloor_room (registerBound C E m d : ℕ) :
    max registerBound (2*(m+d)+1) + (polyBound C E (m+d)+2) ≤
      twoDimCap lpLength (lpTimeFloor registerBound C E) m d := by
  have h := (twoDimCap_bounds lpLength (lpTimeFloor registerBound C E) m d).1
  rw [lpTimeFloor_value] at h
  omega

/-- The public LP shape gives a fixed input program and an ordinary dimension-polynomial
trace from the original flat LP scalar tape. -/
theorem lpBoot_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (registerBound C E : ℕ) (P : K → Prop) (m d : ℕ) (xs : List K)
    (hlen : xs.length=m*d+m) (hs : ((start [m,d] xs).memory).AllData P) (hz : P 0) :
    let target := lpTimeFloor registerBound C E
    ∃ k≤(twoDimBootPolynomial lpLength target).eval (m+d), Block.Eval (Memory.AllData P)
      (twoDimBoot lpLength target) (start [m,d] xs).memory k
      (start (Odd.finiteDims (twoDimCap lpLength target m d) [] [m,d]) (Odd.finiteScalars [] xs)).memory := by
  exact twoDimBoot_correct lpLength (lpTimeFloor registerBound C E) P m d xs (by simpa using hlen) hs hz

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
