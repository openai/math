import OAI.Hierarchy.DescentOrdinaryBornChart
import OAI.Hierarchy.DescentOperandFamilyBook

namespace OAI
/-! # Physical extent of one column for each donor and party -/
namespace Hierarchy.DescentOrdinaryPaletteBirth
open DescentOrdinaryBorn ProtocolRAM
noncomputable section
variable (B : Chart)
def fields :=B.donors*6
def bookWords :=DescentOperandFamilyBook.words (fields B) 1 B.chipBits B.lanes
def output (at_ : ℕ) :=at_+bookWords B
def extent := bookWords B+fields B*B.pitch
def roof (at_ : ℕ) := output B at_+fields B*B.pitch
def bank (at_ : ℕ) (i : Fin (fields B)) : Bank :=⟨output B at_+i.val*B.pitch,Nat.clog 2 B.rows⟩
theorem translated (at_ : ℕ) : roof B at_=at_+extent B :=by simp [roof,output,extent,Nat.add_assoc]
theorem order (at_ : ℕ) : at_≤output B at_ ∧ output B at_≤roof B at_:=⟨Nat.le_add_right ..,Nat.le_add_right ..⟩

end
end Hierarchy.DescentOrdinaryPaletteBirth

end OAI
