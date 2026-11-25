import OAI.Hierarchy.DescentDatedResetOperands
import OAI.Hierarchy.DescentResetKeptWidth

namespace OAI
/-! # Executing the prepared seven-field operand scan at the actual end of the signed publication -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentPackedZip DescentResetOperandSetup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (v : ResetOutput)
local notation "A" => v.receiver


def wholeOperands (s : v.OperandInputs) (r : v.RenderInputs) (base w : ℕ)
    (bank : v.setup.Sources) (laws : v.setup.Laws) : Code w :=
  ((v.setup.code (v.operandFloor base) w bank laws).join (v.keepBook base w)).join
    ⟨v.operandProgram s r base w,v.operandTicks s r base,v.operandMemory s r base⟩

def wholeOperandProgram (s : v.OperandInputs) (r : v.RenderInputs) (base w : ℕ)
    (bank : v.setup.Sources) (laws : v.setup.Laws) :=(v.wholeOperands s r base w bank laws).program
def wholeOperandTicks (s : v.OperandInputs) (r : v.RenderInputs) (base w : ℕ)
    (bank : v.setup.Sources) (laws : v.setup.Laws) :=(v.wholeOperands s r base w bank laws).time
def wholeOperandMemory (s : v.OperandInputs) (r : v.RenderInputs) (base : ℕ) {w : ℕ}
    (bank : v.setup.Sources) (laws : v.setup.Laws) :=(v.wholeOperands s r base w bank laws).image

theorem wholeOperand_any {w : ℕ} (s : v.OperandInputs) (r : v.RenderInputs) (base : ℕ) (m : Memory w)
    (bank : v.setup.Sources) (laws : v.setup.Laws)
    (before : v.setup.Ready bank w (v.operandFloor base))
    (early : v.OperandEarly s r w base) (room : v.scalarEnd base<2^w) :
    (v.wholeOperandProgram s r base w bank laws).Exec m (v.wholeOperandMemory s r base bank laws m)
      (v.wholeOperandTicks s r base w bank laws) ∧
    (∀a,a<v.operandFloor base ∨ v.scalarEnd base≤a →
      v.wholeOperandMemory s r base bank laws m a=m a) ∧
    CheapCode (v.wholeOperandProgram s r base w bank laws) :=by
  obtain ⟨a,b⟩:=v.operand_order base
  have start : v.operandFloor base≤v.keepBase base:=by
    change _≤v.setup.endAddress (v.operandFloor base)
    rw [v.setup.affine]
    exact Nat.le_add_right ..
  have more:=v.keep_before base
  have space:=(a.trans b).trans_lt room
  have phase:=v.setup.any (v.operandFloor base) m bank laws before (more.trans_lt space)
  let held:=(v.setup.code (v.operandFloor base) w bank laws).image m
  have mounted:=v.keep_any base held space
  have both:=Code.combined phase mounted start more
  let ready:=(v.keepBook base w).image held
  have placed:=v.operand_any s r base ready early room
  have scan : Code.Runs ⟨v.operandProgram s r base w,v.operandTicks s r base,v.operandMemory s r base⟩
      (v.operandStart base) (v.scalarEnd base) ready := ⟨placed.1,placed.2.2,placed.2.1⟩
  have done_:=Code.combined both scan (start.trans more) (a.trans b)
  exact ⟨done_.exec,done_.frame,done_.cheap⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
