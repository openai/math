import OAI.Hierarchy.DescentReturnTailNumbers
import OAI.Hierarchy.DescentReturnSharedPages

namespace OAI
/-! # One calibrated rate for the full successor, metadata, final operands, and count -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentDatedAddressBook.MaterialProgram Filter
def endRate (a : ℕ) := 40+6*(a+1)

theorem end_rate (J a : ℕ) : 1000000000000*(scale J a+1)^6≤ scale J (endRate a) :=by
  have one : 1≤ scale J a:=Nat.two_pow_pos _
  have twice : 2*scale J a≤ scale J (a+1):=by
    change 2*2^(a*(J+1))≤2^((a+1)*(J+1))
    rw [Nat.mul_comm,←pow_succ]
    apply Nat.pow_le_pow_right (by decide)
    rw [Nat.add_mul,Nat.one_mul];omega
  have c : 1000000000000≤ scale J 40:=(by decide : 1000000000000≤2^40).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    _ ≤ scale J 40*(scale J (a+1))^6:=Nat.mul_le_mul c (Nat.pow_le_pow_left (by omega : scale J a+1≤ scale J (a+1)) 6)
    _ = scale J (endRate a):=by unfold scale endRate;rw [←pow_mul,←pow_add];congr 1;ring

theorem scheduled_tail_funding {F : Type} [Field F] (G : DescentSixParty.PoweredGadget F) (t f g reset ratio a saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀J M tail i fee : ℕ,J≤Nat.log 2 h → 2^h≤2*M →
      let S:=DescentSixParty.stageNumbers G t J f g reset M tail
      let R:=ratio*scale J (endRate a)
      fee≤R*purchased (S.hostSize i) (S.groupCount i) h →
      fee≤S.hostSize i*h*(R+1)+S.hostSize i*(S.groupCount i*S.radix)*R :=
  signed_date_funded_at G t f g reset ratio (endRate a) saving

end Hierarchy.DescentCompiler.TerminalScale

end OAI
