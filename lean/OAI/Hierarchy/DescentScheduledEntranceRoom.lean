import OAI.Hierarchy.DescentScheduledCanvasRoom
import OAI.Hierarchy.DescentScheduledRepackKey
import OAI.Hierarchy.DescentOriginalResetBounds

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler TerminalScale DescentSixParty DescentSixParty.PackedFlow.Canvas DescentPackedWalsh
open DescentPackedFlowPublication DescentWalshPrecision ProtocolRAM Filter
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset τ B drift : ℕ) {ι : ℕ→Type*}
    (sites age p degree inputBits numberBits oldOperand oldPrimitive floor : ∀h,ι h→ℕ)
    (ordinary : ∀h,ι h→ℕ→Dated.Ordinary) (old : ∀h,ι h→StageVenueTail.Date)
    (wire : ∀h,ι h→ℕ→ℕ→Bank) (roster : ∀h,ι h→Bank)
local notation "J" h:arg => Nat.log 2 h/(2*B)
local notation "tb" h:arg => tail τ (J h)
local notation "S" h:arg i:arg => stageNumbers G t (J h) f g reset (sites h i) (tb h)
local notation "k" h:arg => groupBits t (J h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "a" h:arg i:arg => scheduled G (S h i) board (k h) (tb h) (age h i) (p h i) f g drift (degree h i) h
  (ordinary h i) op (inputBits h i) (numberBits h i) (oldOperand h i) (oldPrimitive h i) (old h i)
  (wire h i) (roster h i) (floor h i)
local notation "c" h:arg i:arg => (S h i).groupWidth (k h) (tb h) (age h i)
local notation "m" h:arg i:arg => c h i+k h
local notation "b" h:arg i:arg => (S h i).localWalshBits (p h i) (m h i) f (quota t)
local notation "l" h:arg i:arg => laneBits (m h i) h (b h i)
local notation "P" h:arg i:arg => (a h i).chart ((a h i).stageStart (floor h i))

theorem scheduled_entrance (D : ℕ) (source : Bounded sites) (den : 0 < B)
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g) ≤ B)
    (height : ∀h i,age h i ≤ (S h i).length) (payload : ∀h i,p h i ≤ h)
    (branch : ∀h i,(old h i).degree ≤ D) : ResetOutput.EntranceRoom (fun h i=>a h i) floor := by
  obtain ⟨canvas,radix,axes,groups,lanes⟩:=scheduled_canvas_room G board op t f g reset τ B drift sites age p degree
    inputBits numberBits oldOperand oldPrimitive floor ordinary old wire roster D source height payload branch
  have book:=scheduled_initial_book G board op t f g reset τ B drift sites age p degree inputBits numberBits
    oldOperand oldPrimitive floor ordinary old wire roster D den cutoff height payload branch
  refine ⟨canvas,radix,axes,book,groups,lanes,?_⟩
  filter_upwards [scheduled_repack_dictionary G board op t f g reset τ B cutoff] with h dict
  intro i
  exact dict (sites h i) (age h i) (p h i) drift (degree h i) (ordinary h i) (old h i)
    (inputBits h i) (numberBits h i) (oldOperand h i) (oldPrimitive h i) (floor h i) (wire h i) (roster h i)
    (height h i) (payload h i)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
