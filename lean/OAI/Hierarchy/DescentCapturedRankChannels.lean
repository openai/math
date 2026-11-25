import OAI.Hierarchy.DescentPhysicalMixedCapture

namespace OAI
/-! The original scalar directory and raw operand page at each real compact receiver. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentPackedZip DescentSixParty.Chronology DescentSIMDLookup DescentResetLocalRoster
open DescentResetDenseOperand ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "V₀" => a.successor
local notation "b₀" => a.rebased floor
local notation "F₀" => (V₀).front
local notation "P₀" => (F₀).peer
local notation "S₀" => (V₀).issuedScene b₀ u.earlier
local notation "E₀" => (V₀).actorEnd b₀
local notation "C₀" => (F₀).contactLayout E₀
local notation "Q₀" => (V₀).privateShape
local notation "K₀" => (V₀).contactShape
local notation "D₀" => u.masked
local notation "regs₀" => (V₀).jointRegisters b₀ u.earlier
local notation "T₀" => (V₀).trunkEnd b₀
local notation "M₀" => (V₀).massEnd b₀
local notation "J₀" => (V₀).jointEnd b₀
local notation "don₀" => (F₀).donorStart E₀
local notation "scene₀" m => ((F₀).trunkScene E₀ S₀ u.sceneFits).image m

variable {u} {N : ℕ} (R : u.MeasuredChannels N) (m : Memory w) (seen : CaptureRoom R m)

include seen in
theorem MeasuredChannels.scalar_at (h : Fin (D₀).hosts) (g : Fin (D₀).groups) (j : Fin 4) :
    (R.capturedChannels.peer j h g).val=DescentResetPeerJointRAM.value (P₀).oldHosts (P₀).shapes
      (P₀).oldDegree R.prior N R.names R.now h j ∧
    (R.capturedChannels.aux j h g).val=DescentResetPeerJointPacked.Aux.value (P₀).shapes R.names R.prior R.near h j:=by
  constructor
  · exact Nat.mod_eq_of_lt (DescentResetPeerJointRAM.value_lt R.prior R.names R.now h j seen.distinct seen.shapes seen.keys)
  · exact Nat.mod_eq_of_lt (DescentResetPeerJointPacked.Aux.value_lt (P₀).shapes R.names R.prior R.near h j seen.distinct seen.shapes seen.keys seen.previousSelf)

theorem MeasuredChannels.contact_at (h : Fin N) (g : Fin (D₀).groups) (x : Fin (K₀).blocks)
    (q : Fin (K₀).sockets) (j : Fin 4) :
    dense R.names (R.capturedChannels.contact x q j) (h.castLE seen.used) g =
      R.contactValues q j ((R.names h).cast R.slots) ((finProdFinEquiv (g,x)).cast R.coarse.symm):=by
  simp only [dense, Fin.val_castLE, dite_eq_left h.isLt]
  rfl

theorem MeasuredChannels.private_at (h : Fin N) (g : Fin (D₀).groups) (x : Fin (Q₀).blocks)
    (q : Fin (Q₀).keys) (j : Fin 3) :
    dense R.names (R.capturedChannels.privateFields x q j) (h.castLE seen.used) g =
      (Q₀).measured C₀ R.rootWords q j ((R.names h).cast R.hosts) ((finProdFinEquiv (g,x)).cast R.groups):=by
  simp only [dense, Fin.val_castLE, dite_eq_left h.isLt]
  rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
