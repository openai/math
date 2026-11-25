import Mathlib.Tactic

namespace OAI
/-! # Arithmetic for the full native host invoice -/
namespace Hierarchy.DescentSixParty.SeedNamed

/-- The three constants price the original seed circuit, immutable input and
native programs separately. The coefficient includes the actual hardware price. -/
def earnedHostPrice (circuit input programs ratio implementation : ℕ) :=
  circuit+9*input+192*(ratio+1)+implementation*5000*(programs+input+64)

theorem earned_host_invoice (h w rate T fund sites seed firstFree native pcs regs fuel observations
    raw width bins slots price circuit input programs:ℕ)
    (widthRoom:width≤ h+1) (bus:w≤ rate*h) (sitesPos:0< sites) (offered:2^h≤ sites)
    (source:seed*T≤ circuit*fund) (table:firstFree*(h+1)*T≤ input*fund)
    (runtime:native*(h+1)*T≤ programs*fund) (inventory:sites*(h+1)*T≤64*fund)
    (rawPaid:raw≤ firstFree) (keys:bins≤ sites) (pool:slots≤ native)
    (observed:observations=raw+(1+bins+1))
    (cpu:pcs+regs+fuel≤ native+4176+100*raw+6*bins+300*slots) :
    (seed+9*(raw*width)+(1+bins+1)*(w+1)+
      price*(pcs+regs+firstFree+fuel+observations+2^h+1)*(h+1))*T≤
      earnedHostPrice circuit input programs rate price*fund :=by
  have inputs:raw*width*T≤ input*fund:=
    (Nat.mul_le_mul_right T (Nat.mul_le_mul rawPaid widthRoom)).trans table
  have bitWidth:w+1≤(rate+1)*(h+1):=by nlinarith only [bus,Nat.zero_le rate,Nat.zero_le h]
  have keyCount:1+bins+1≤3*sites:=by omega
  have readout : (1+bins+1)*(w+1)*T≤192*(rate+1)*fund:=calc
    _ ≤ (3*sites)*((rate+1)*(h+1))*T:=Nat.mul_le_mul_right _ (Nat.mul_le_mul keyCount bitWidth)
    _ = 3*(rate+1)*(sites*(h+1)*T):=by ring
    _ ≤ 3*(rate+1)*(64*fund):=Nat.mul_le_mul_left _ inventory
    _ = _:=by ring
  have words : pcs+regs+firstFree+fuel+observations+2^h+1≤5000*(native+firstFree+sites):=by omega
  have code : (pcs+regs+firstFree+fuel+observations+2^h+1)*(h+1)*T≤5000*(programs+input+64)*fund:=calc
    _ ≤ 5000*(native+firstFree+sites)*(h+1)*T:=Nat.mul_le_mul_right T (Nat.mul_le_mul_right (h+1) words)
    _ = 5000*(native*(h+1)*T+firstFree*(h+1)*T+sites*(h+1)*T):=by ring
    _ ≤ 5000*(programs*fund+input*fund+64*fund):=
      Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.add_le_add runtime table) inventory)
    _ = _:=by ring
  calc
    _ = seed*T+9*(raw*width*T)+(1+bins+1)*(w+1)*T+
      price*((pcs+regs+firstFree+fuel+observations+2^h+1)*(h+1)*T):=by ring
    _ ≤ circuit*fund+9*(input*fund)+192*(rate+1)*fund+price*(5000*(programs+input+64)*fund):=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add source (Nat.mul_le_mul_left _ inputs)) readout)
        (Nat.mul_le_mul_left _ code)
    _ = _:=by unfold earnedHostPrice;ring

end Hierarchy.DescentSixParty.SeedNamed

end OAI
