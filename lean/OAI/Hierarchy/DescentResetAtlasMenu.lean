import OAI.Hierarchy.DescentResetAtlasDirections
import OAI.Hierarchy.DescentRecordedRotorLayers
import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! The finite rotor opcodes, layer budget and batch width of a dated reset. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.Atlas
open DescentSixParty DescentResetGates DescentPackedResetRotorRoles DescentSIMDLookup
open ProtocolRAM
noncomputable section

def roleCode (n : ℕ) (t : CanonicalTag (2^n)) : Cell (roleBits n) :=
  ⟨role t,by
    cases t with
    | inl rotor=>exact number_lt rotor.1 rotor.2
    | inr digit=>
      have six : 6<2^(roleBits n) := (by decide : 6<2^3).trans_le (Nat.pow_le_pow_right (by decide) (by unfold roleBits;omega))
      exact (short_lt digit).trans six⟩

theorem roleCode_injective (n : ℕ) : Function.Injective (roleCode n) :=fun _a _b eqn=>
  role_injective n (congrArg Fin.val eqn)

variable (a : PhysicalReset) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ)
local notation "P" => a.stencilPhase sh floor count hub g Y
local notation "n" => a.successor.middle.rotorBits

/-- Publicly selected stage parameters determine every coded rotor input. -/
def menu {h : ℕ} (board : NonlinearExpanders.Graph n h) (degree : (P).S.degree=a.ports)
    (packet C gain factor : ℕ) : a.Atlas :=
  let cap:=a.c/2
  fromStencil a sh floor count hub g Y degree h (roleBits n) board packet C gain
    (DescentRecordedRotorLayers.layers n packet a.depthCut cap*gain)
    (DescentRecordedRotorLayers.width a.depthCut cap) factor (roleCode n)

theorem layer_slot {h : ℕ} (board : NonlinearExpanders.Graph n h) (degree : (P).S.degree=a.ports)
    (packet C gain factor : ℕ) (i : Fin (DescentRecordedRotorLayers.layers n packet a.depthCut (a.c/2)))
    (j : Fin gain) :
    i.val*gain+j.val < (menu a sh floor count hub g Y board degree packet C gain factor).batches := by
  change i.val*gain+j.val< _*gain
  exact (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right gain i.isLt)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.Atlas

end OAI
