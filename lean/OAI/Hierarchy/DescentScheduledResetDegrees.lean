import OAI.Hierarchy.DescentCalibratedResetChart

namespace OAI
/-! # One reset word size for the finite set of attained incoming degrees -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler DescentSixParty DescentCompiler.TerminalScale DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset τ maximum drift : ℕ)

def degreeRate :=
  Finset.univ.sup (fun D : Fin (maximum+1)=>ResetOutput.receiverRate G board op t f g reset D.val)
local notation "rate₀" => degreeRate G board op t f g reset maximum

theorem scheduled_all_tables (B bound : ℕ) (positive : 0<B) (bought : 2*(rate₀)≤B)
    (branch : G.b≤2^(capRate G t g)) :
    ∀ᶠ h : ℕ in atTop,let j:=Nat.log 2 h/(2*B);
    ∀sites age p degree : ℕ, let S:=stageNumbers G t j f g reset sites (tail τ j)
    let k:=groupBits t j S.hostGain S.capGain (cutRate t f g)
    ∀(ordinary : ℕ→Dated.Ordinary) (old : StageVenueTail.Date) (operandLanes primitiveLanes base : ℕ)
      (addr : ℕ→ℕ→Bank) (roster : Bank),
      p≤h→degree≤bound→ old.degree≤ maximum→ old.cap=((capCalendar G.b t g j).take age).prod*256→
      old.paidBits=S.censusBits p→
      let a:=scheduled G S board k (tail τ j) age p f g drift degree h ordinary op
        (S.firstWidth G.b p) (S.grainAt G.b p 0) operandLanes primitiveLanes old addr roster base
      ∀bits,bits∈a.successor.rootUnits ∨ bits∈a.successor.receiverUnits →
        bits*a.successor.receiver.lanes≤h/2 :=by
  have each (D : Fin (maximum+1)) : 2*ResetOutput.receiverRate G board op t f g reset D.val≤B :=
    (Nat.mul_le_mul_left 2 (Finset.le_sup (f:=fun x : Fin (maximum+1)=>
      ResetOutput.receiverRate G board op t f g reset x.val) (Finset.mem_univ D))).trans bought
  filter_upwards [Filter.eventually_all.mpr (fun D : Fin (maximum+1)=>
    scheduled_tables G board op t f g reset τ D.val drift B positive (each D) branch bound)] with h hw
  dsimp only
  intro sites age p degree ordinary old A M base addr roster hp hd hD hc hP
  exact hw ⟨old.degree,Nat.lt_succ_of_le hD⟩ sites age p degree ordinary old A M base addr roster hp hd rfl hc hP

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
