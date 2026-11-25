import OAI.Hierarchy.DescentCalendarNumbers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI
/-! # Spending the actual terminal common-position shelf on the chosen copy schedule -/

namespace Hierarchy.DescentSixParty
open DescentCompiler
open scoped BigOperators
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The reserve per common position includes the complete group tail and the true
hub-growth allowance. Only one name is stored at a position for all residual blocks. -/
theorem terminal_host_balance (t J f g reset M tail : ℕ) :
    let S:=stageNumbers G t J f g reset M tail
    S.hostSize S.length*2^J*2^tail*2^(S.capGain*S.length+8+cutRate t f g)=M*S.copies := by
  let c:=hostRate t reset
  let e:=capRate G t g
  let l:=(t+1)*J
  let cut:=cutRate t f g
  let k:=groupBits t J c e cut
  change M*(2^c*2^k)^l*2^J*2^tail*2^(e*l+8+cut)=M*(2^tail*(2^k)^(l+1))
  rw [mul_pow,pow_succ,←pow_mul]
  have key : 2^k=2^(c*l)*2^J*2^(e*l+8+cut) := by
    rw [←pow_add,←pow_add]
    congr 1
    dsimp [k,groupBits,l]
    ring
  calc
    _ = M*(2^tail*((2^k)^l*(2^(c*l)*2^J*2^(e*l+8+cut)))) := by ring
    _ = _ := by rw [←key]

/-- Charge an integral high-word tariff against the genuine terminal budget.
The declared count is an upper bound on common points, independently of the group multiplicity. -/
theorem terminal_host_price (t J f g reset M tail h p charge : ℕ)
    (payment : charge*h≤p*(2^tail*2^(capRate G t g*((t+1)*J)+8+cutRate t f g))) :
    let S:=stageNumbers G t J f g reset M tail
    S.hostSize S.length*charge*h*2^J≤M*(S.copies*p) := by
  let S:=stageNumbers G t J f g reset M tail
  have receipt:=terminal_host_balance G t J f g reset M tail
  change S.hostSize S.length*2^J*2^tail*2^(S.capGain*S.length+8+cutRate t f g)=M*S.copies at receipt
  calc
    _ = (S.hostSize S.length*2^J)*(charge*h) := by ring
    _ ≤ (S.hostSize S.length*2^J)*(p*(2^tail*2^(S.capGain*S.length+8+cutRate t f g))) :=
      Nat.mul_le_mul_left _ payment
    _ = (S.hostSize S.length*2^J*2^tail*2^(S.capGain*S.length+8+cutRate t f g))*p := by ring
    _ = _ := by rw [receipt,Nat.mul_assoc]

end Hierarchy.DescentSixParty

end OAI
