import OAI.Hierarchy.DescentSignedReturnPopulation
import OAI.Hierarchy.DescentOrdinarySharedLedger

namespace OAI
/-! # Uniform price of the signed prefix's shared literal tables -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentSixParty DescentDatedAddressBook DescentSIMDLookup Filter

/-- The source may be as small as half of the height bin. Raising the savings
exponent by one absorbs that factor for every bin, including the initial age. -/
theorem signed_half_pages (ratio rate saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀J M : ℕ,J≤Nat.log 2 h → 2^h≤2*M →
      (ratio*scale J rate)*MaterialProgram.halfPages h≤M/(2^J)^saving :=by
  filter_upwards [Overlap.charged_half_pages ratio rate 1 (saving+1),eventually_ge_atTop 2] with h mount tall
  intro J M age size
  let I:=max 1 J
  have fits:I≤Nat.log 2 h:=max_le (Nat.le_log_of_pow_le (by decide) (by simpa using tall)) age
  have up:J≤I:=le_max_right ..
  have exp : rate*(J+1)≤rate*(I+1)^1:=by simpa using Nat.mul_le_mul_left rate (Nat.succ_le_succ up)
  have task:=mount I (rate*(J+1)) (2*M) fits exp size
  have pitch : 2≤2^I :=by simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (le_max_left 1 J)
  have key:(2^J)^saving*2≤(2^I)^(saving+1):=by
    rw [pow_succ];exact Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) up) _) pitch
  have actual:=Nat.div_mul_le_self (2*M) ((2^I)^(saving+1))
  have old : ((2*M)/(2^I)^(saving+1))*((2^J)^saving)*2≤2*M:=
    (by rw [Nat.mul_assoc];exact (Nat.mul_le_mul_left _ key).trans actual)
  have result : (2*M)/(2^I)^(saving+1)≤M/(2^J)^saving:=
    (Nat.le_div_iff_mul_le (by positivity)).2 (by omega)
  exact (show (ratio*scale J rate)*MaterialProgram.halfPages h≤(2*M)/(2^I)^(saving+1) from
    by simpa only [scale,MaterialProgram.halfPages,Nat.mul_assoc] using task).trans result

theorem signed_date_funded_at {F : Type} [Field F] (G : PoweredGadget F) (t f g reset ratio rate saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀J M tail i fee : ℕ,J≤Nat.log 2 h → 2^h≤2*M →
      let S:=stageNumbers G t J f g reset M tail
      let R:=ratio*scale J rate
      fee≤R*MaterialProgram.purchased (S.hostSize i) (S.groupCount i) h →
      fee≤S.hostSize i*h*(R+1)+S.hostSize i*(S.groupCount i*S.radix)*R :=by
  filter_upwards [signed_half_pages ratio rate saving,eventually_ge_atTop 1] with h mounts positive
  intro J M tail i fee age size S R exactFee
  have page:=mounts J M age size
  have slot:S.groupCount i≤S.groupCount i*S.radix:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  apply schedule_receipt G t f g reset J M tail h R R saving positive i fee
  apply exactFee.trans
  unfold MaterialProgram.purchased
  calc
    _=S.hostSize i*h*R+S.hostSize i*S.groupCount i*R+R*MaterialProgram.halfPages h:=by ring
    _≤_:=Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right R (Nat.mul_le_mul_left _ slot)) _) page

end Hierarchy.DescentCompiler.TerminalScale

end OAI
