import OAI.Hierarchy.CheapISAHostClock
import OAI.Hierarchy.DescentFixedISATariff
import OAI.Hierarchy.DescentOpenStageCount
import OAI.Hierarchy.DescentTerminalChartScale
import OAI.Hierarchy.Catalyst

namespace OAI
/-! # Physical instruction, register and time widths from the terminal host bill -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Catalyst Filter
open ThreeFlat.Routing
open scoped Classical

variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The record time and address limits of the fixed ISA follow from the same
invoice used to fund the terminal host. Its exterior arity is counted in the
original approximation's size. -/
theorem wide_host_isa_room (t f g reset τ price : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ J M s w pcs regs firstFree fuel obs extra rate : ℕ,
    ∀{cp pins : ℕ} (X : Approximation F cp pins),
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let E:=Fintype.card (Port pins X.width)
      J≤Nat.log 2 h → M≤(2^h)^2 → 10*(X.size+1)≤M → s≤h → 3*h≤w →
      (extra+
        (257*(1000*(2*(7*(rate+6))+2)*(2*4^7+1))+256*fixedISAPrice*(rate+6))*
          (pcs+regs+firstFree+fuel+obs+2^h+1)*(h+1))*2^J≤price*(S.copies*s)*(M+2^J*E) →
      pcs≤2^(w+1) ∧ regs≤2^(w+1) ∧ CheapISA.hostFuel fuel+obs≤2^(CheapISA.width w+1) ∧
        (CheapISA.dataBase pcs regs+firstFree)+(CheapISA.hostFuel fuel+obs)≤2^(3*h) :=by
  filter_upwards [stage_open_record_capacity G t f g reset τ (256*price) 0] with h storage
  intro J M s w pcs regs firstFree fuel obs extra rate cp pins X S E age upper original bits wide bill
  let T:=2^J
  let n:=pcs+regs+firstFree+fuel+obs+2^h+1
  let size:=(CheapISA.dataBase pcs regs+firstFree)+(CheapISA.hostFuel fuel+obs)
  let coefficient:=257*(1000*(2*(7*(rate+6))+2)*(2*4^7+1))+256*fixedISAPrice*(rate+6)
  have units : 0<coefficient:=by dsimp only [coefficient];positivity
  have time : n≤extra+coefficient*n*(h+1):=
    ((Nat.le_mul_of_pos_left _ units).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos h))).trans (Nat.le_add_left ..)
  have observed : n*T≤price*(S.copies*s)*(M+T*E):=(Nat.mul_le_mul_right T time).trans bill
  have pinsFit : E≤M:=by
    have count : E≤X.size:=Nat.le_add_left ..
    omega
  have pos : 0<T:=Nat.two_pow_pos _
  have ambient : M+T*E≤(2*M)*T:=calc
    _ ≤ M*T+T*M := Nat.add_le_add (Nat.le_mul_of_pos_right _ pos) (Nat.mul_le_mul_left T pinsFit)
    _ = _ :=by ring
  have clock : n≤price*(S.copies*s)*(2*M):=by
    apply Nat.le_of_mul_le_mul_right (c:=T) _ pos
    calc
      n*T ≤ price*(S.copies*s)*(M+T*E) := observed
      _ ≤ price*(S.copies*s)*((2*M)*T) := Nat.mul_le_mul_left _ ambient
      _ = _ :=by ac_rfl
  have instruction : size≤128*n:=by
    have powPos : 0<(2:ℕ)^h:=Nat.two_pow_pos h
    dsimp only [size,CheapISA.dataBase,CheapISA.regBase,CheapISA.hostFuel,n]
    omega
  have written : size≤2^(3*h):=by
    apply storage J M M s size age upper bits
    calc
      size ≤ 128*n := instruction
      _ ≤ 128*(price*(S.copies*s)*(2*M)) := Nat.mul_le_mul_left 128 clock
      _ = (256*price)*(h+1)^0*M*(S.copies*s) :=by ring
  have labels : pcs≤ size:=by dsimp only [size,CheapISA.dataBase,CheapISA.regBase];omega
  have registers : regs≤ size:=by dsimp only [size,CheapISA.dataBase,CheapISA.regBase];omega
  have ticks : CheapISA.hostFuel fuel+obs≤ size:=Nat.le_add_left ..
  have operands : 2^(3*h)≤2^(w+1):=Nat.pow_le_pow_right (by decide) (wide.trans (Nat.le_succ _))
  have counter : 2^(3*h)≤2^(CheapISA.width w+1):=
    Nat.pow_le_pow_right (by decide) (by dsimp only [CheapISA.width];omega)
  exact ⟨labels.trans (written.trans operands),registers.trans (written.trans operands),
    ticks.trans (written.trans counter),written⟩

end Hierarchy.DescentSixParty

end OAI
