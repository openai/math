import OAI.Hierarchy.DescentDatedPhysicalOrdinary
import OAI.Hierarchy.DescentDatedOperandAny
import OAI.Hierarchy.DescentDatedOperandPrice

namespace OAI
/-! # The physical ordinary date's seven-field operand suffix at its genuine paid address -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedOperand
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (t : DescentDatedPriorOperand.Banks v.resolver)

def operandProgram (w floor : ℕ) :=t.program w (v.normalizedEnd floor)
def operandTicks (floor : ℕ) :=t.ticks (v.normalizedEnd floor)
def operandState {w : ℕ} (floor : ℕ) (m : Memory w) :=t.result (v.normalizedEnd floor) m

/-- Truth of the semantic input tables is used only by the proof. The compiled
program and its clock depend on the public dimensions and old absolute banks. -/
theorem operand_run {w : ℕ} (floor : ℕ) (sources : Fin v.resolver.jobs→DescentDatedPriorOperand.Source v.resolver) (m : Memory w)
    (early : t.Early (v.normalizedEnd floor) w) (raw : t.Registered sources m)
    (high : v.endAddress floor<2^w) (positive : 0<v.resolver.lanes)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2) :
    let done:=v.operandState t floor m;let cpu:=v.operandProgram t w floor
    cpu.Exec m done (v.operandTicks t floor) ∧
    (∀j,DescentDatedPriorOperand.Banks.Returned sources positive (v.normalizedEnd floor) j done) ∧
    (∀a,a<v.normalizedEnd floor ∨ v.endAddress floor≤a→done a=m a) ∧ CheapCode cpu :=
  t.run sources m early raw high positive wide

theorem operand_any {w : ℕ} (floor : ℕ) (m : Memory w) (early : t.Early (v.normalizedEnd floor) w)
    (high : v.endAddress floor<2^w) (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2) :
    let done:=v.operandState t floor m;let cpu:=v.operandProgram t w floor
    cpu.Exec m done (v.operandTicks t floor) ∧ (∀a,a<v.normalizedEnd floor ∨ v.endAddress floor≤a→done a=m a) ∧ CheapCode cpu :=
  t.any m early high wide

theorem operand_price {ι : ℕ→Type*} (v : ∀h,ι h→PhysicalOrdinary F P)
    (room : DescentDatedPriorOperand.Layout.ScalarRoom (fun h i=>(v h i).resolver))
    (t : ∀h i,DescentDatedPriorOperand.Banks (v h i).resolver) (floor width : ∀h,ι h→ℕ) :
    Bounded (fun h i=>(v h i).operandTicks (t h i) (floor h i)) ∧
    Bounded (fun h i=>DescentStaticWordColumn.names ((v h i).operandProgram (t h i) (width h i) (floor h i))) :=
  DescentDatedPriorOperand.Layout.program_rates _ room t (fun h i=>(v h i).normalizedEnd (floor h i)) width

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
