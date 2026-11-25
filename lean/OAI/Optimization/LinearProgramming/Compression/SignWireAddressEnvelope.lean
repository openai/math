import OAI.Optimization.LinearProgramming.RAM.CallableOddBase
import OAI.Optimization.LinearProgramming.RAM.Footprint

/-! The doubled register layout has an address envelope over every base type. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM RAM.Callable

/-- The request packet starts just past the resident cache, followed by the decoded
row and the answer packet. -/
def callbackSend (cap : ℕ) := 2*cap+1
def callbackRow (n fuel cap : ℕ) := callbackSend cap+(n+1)*(2*(fuel+1)+2)
def callbackReply (n fuel cap : ℕ) := callbackRow n fuel cap+(n+1)

theorem cacheImage_address {K : Type*} [Zero K] {old m : Memory K} {C R : ℕ}
    (oldBound : Footprint C (old.atPC 0)) (callerBound : ∀ j,m.index j ≤ R) (i : ℕ) :
    (Odd.memory old m).index i ≤ max (2*C) (2*R+1) := by
  by_cases h : i%2=0
  · have eq : 2*(i/2)=i := by omega
    rw [← eq,Odd.index_even]
    exact (Nat.mul_le_mul_left 2 (oldBound.address _)).trans (le_max_left ..)
  · have eq : Odd.slot (i/2)=i := by dsimp [Odd.slot];omega
    rw [← eq,Odd.index_slot]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (callerBound _)) 1).trans (le_max_right ..)

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
