import OAI.Hierarchy.DescentResetReceiverDensity
import OAI.Hierarchy.DescentScheduledResetDegrees

namespace OAI
/-! # Uniform packing of the actual reset's two persistent output words -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler DescentSixParty DescentCompiler.TerminalScale DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset τ maximum drift : ℕ)
def allDensityRate :=
  Finset.univ.sup (fun D : Fin (maximum+1)=>densityRate G board op t f g reset D.val)

structure DensityCalendar (B bound h : ℕ) : Prop where
  written :
    let J:=Nat.log 2 h/(2*B)
    ∀sites age p degree : ℕ, let S:=stageNumbers G t J f g reset sites (tail τ J)
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    ∀(ordinary : ℕ→Dated.Ordinary) (old : StageVenueTail.Date) (A M base : ℕ) (addr : ℕ→ℕ→Bank) (roster : Bank),
    age≤S.length → p≤h → degree≤bound → old.degree≤ maximum →
    old.cap=((capCalendar G.b t g J).take age).prod*256 → old.paidBits=S.censusBits p →
    let a:=scheduled G S board k (tail τ J) age p f g drift degree h ordinary op
      (S.firstWidth G.b p) (S.grainAt G.b p 0) A M old addr roster base
    let L:=a.successor.receiver.lanes
    S.groupCount (age+1)≤L ∨ h≤L*scale J (allDensityRate G board op t f g reset maximum)

theorem eventual_density_calendar (B bound : ℕ) (positive : 0<B) (bought : 2*degreeRate G board op t f g reset maximum≤B)
    (branch : G.b≤2^(capRate G t g)) :
    ∀ᶠ h : ℕ in atTop,DensityCalendar G board op t f g reset τ maximum drift B bound h :=by
  have each (D : Fin (maximum+1)) : 2*ResetOutput.receiverRate G board op t f g reset D.val≤B :=
    (Nat.mul_le_mul_left 2 (Finset.le_sup (f:=fun x : Fin (maximum+1)=>
      ResetOutput.receiverRate G board op t f g reset x.val) (Finset.mem_univ D))).trans bought
  filter_upwards [Filter.eventually_all.mpr (fun D : Fin (maximum+1)=>
    scheduled_density G board op t f g reset τ D.val drift B positive (each D) branch bound)] with h receipts
  constructor
  dsimp only
  intro sites age p degree ordinary old A M base addr roster dated hp hd fit cap paid
  let D : Fin (maximum+1):=⟨old.degree,Nat.lt_succ_of_le fit⟩
  have current:=(receipts D sites age p degree ordinary old A M base addr roster dated hp hd rfl cap paid).1
  have up : densityRate G board op t f g reset D.val≤allDensityRate G board op t f g reset maximum :=
    Finset.le_sup (f:=fun x : Fin (maximum+1)=>densityRate G board op t f g reset x.val) (Finset.mem_univ D)
  exact current.imp_right (fun t=>t.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right
    (by decide : 0<(2:ℕ)) (Nat.mul_le_mul_right _ up))))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
