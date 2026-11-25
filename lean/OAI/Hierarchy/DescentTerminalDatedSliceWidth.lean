import OAI.Hierarchy.DescentTerminalSliceWidth
import OAI.Hierarchy.DescentTerminalLastOverlapPitch

namespace OAI
/-! # The actual last dated flat-arity, role and affine strips fit one original ROM -/
namespace Hierarchy.DescentTerminalSliceShelf
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentDatedAddressBook
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Filter
noncomputable section
set_option quotPrecheck false
variable {F:Type} [Field F] (G:PoweredGadget F) {n d:ℕ} (board:NonlinearExpanders.Graph n d)
    (op:RotorSpec) (t f g reset τ D drift B:ℕ)
local notation "σ" => ResetOutput.receiverRate G board op t f g reset D
local notation "α" => 1+operandExponent G (stageNumbers G t 0 f g reset 0 0)
local notation "J_" h:max => Nat.log 2 h/(2*B)
local notation "S_" h:max M:max => stageNumbers G t (J_ h) f g reset M (tail τ (J_ h))
local notation "k_" h:max => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)

theorem named_digits_for (coefficientDegree:ℕ) (branch:G.b≤2^(capRate G t g)) (positive:0<B)
    (bought:2*(τ+(σ+α))≤B) :
    ∀ᶠh:ℕ in atTop,∀sites age p degree (ordinary:ℕ→Dated.Ordinary)
      (old:StageVenueTail.Date) (operandLanes primitiveLanes base:ℕ) (addr:ℕ→ℕ→Bank) (roster:Bank),
      let S:=S_ h sites
      let z:=PhysicalReset.scheduled G S board (k_ h) (tail τ (J_ h)) age p f g drift degree h ordinary op
        (S.firstWidth G.b p) (S.grainAt G.b p 0) operandLanes primitiveLanes old addr roster base
      let v:=z.successor
      let L:=2+3*v.argumentSlots
      let d₀:=physicalWidth (S.groupCount S.length) v.nodes v.primitive.chart.bits v.nodeBits
      p≤h→degree≤coefficientDegree→ old.degree=D→ old.cap=((capCalendar G.b t g (J_ h)).take age).prod*256→
      old.paidBits=S.censusBits p→d₀*L+Nat.clog 2 (L+1)≤h/2 ∧
        DescentTerminalPointerFrame.size L d₀≤2*2^(h/2) := by
  filter_upwards [PhysicalReset.scheduled_scale G board op t f g reset τ D drift B positive branch coefficientDegree,
    attained_digits τ σ α B positive bought,eventually_late (drift+1) B positive] with h measured legal late
  intro sites age p degree ordinary old operandLanes primitiveLanes base addr roster
  dsimp only
  intro grain degreeFit originalDegree cap census
  let S:=S_ h sites
  let v:=(PhysicalReset.scheduled G S board (k_ h) (tail τ (J_ h)) age p f g drift degree h ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) operandLanes primitiveLanes old addr roster base).successor
  have width:=measured sites age p degree ordinary old operandLanes primitiveLanes base addr roster
    grain degreeFit originalDegree cap census
  have capAt:=S.capacities_at_scale G drift 1 (by
    change drift+1≤2^(1*((J_ h)+1))
    rw [Nat.one_mul]
    exact late.trans ((Nat.le_succ _).trans (Nat.lt_two_pow_self (n:=J_ h+1)).le))
  have count:S.groupCount S.length=2^(tail τ (J_ h)):=by simp [S,AtomSchedule.groupCount,stageNumbers]
  have hw:=width_of_reset v (S.groupCount S.length) rfl
  have bound:=legal (S.groupCount S.length) v.argumentSlots
    (physicalWidth (S.groupCount S.length) v.nodes v.primitive.chart.bits v.nodeBits)
    (by rw [count];exact Nat.two_pow_pos _) count.le
    (hw.trans (Nat.mul_le_mul_left _ width)) (by exact capAt.2)
  exact ⟨bound,table_size _ _ _ (by omega) bound⟩

theorem named_digits (branch:G.b≤2^(capRate G t g)) (positive:0<B)
    (bought:2*(τ+(σ+α))≤B) :
    ∀ᶠh:ℕ in atTop,∀sites age p degree (ordinary:ℕ→Dated.Ordinary)
      (old:StageVenueTail.Date) (operandLanes primitiveLanes base:ℕ) (addr:ℕ→ℕ→Bank) (roster:Bank),
      let S:=S_ h sites
      let z:=PhysicalReset.scheduled G S board (k_ h) (tail τ (J_ h)) age p f g drift degree h ordinary op
        (S.firstWidth G.b p) (S.grainAt G.b p 0) operandLanes primitiveLanes old addr roster base
      let v:=z.successor
      let L:=2+3*v.argumentSlots
      let d₀:=physicalWidth (S.groupCount S.length) v.nodes v.primitive.chart.bits v.nodeBits
      p≤h→degree≤D→ old.degree=D→ old.cap=((capCalendar G.b t g (J_ h)).take age).prod*256→
      old.paidBits=S.censusBits p→d₀*L+Nat.clog 2 (L+1)≤h/2 ∧
        DescentTerminalPointerFrame.size L d₀≤2*2^(h/2) :=
  named_digits_for G board op t f g reset τ D drift B D branch positive bought

end
end Hierarchy.DescentTerminalSliceShelf

end OAI
