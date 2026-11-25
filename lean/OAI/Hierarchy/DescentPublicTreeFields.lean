import OAI.Hierarchy.DescentResetRecordedPrimary
import OAI.Hierarchy.DescentPublicRelayPacket

namespace OAI
/-! # Actual public scalar and donor-coordinate ports of the exceptional gate table -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open ProtocolRAM DescentPackedZip DescentSIMDLookup DescentResetPublicOperandBook DescentResetOperandSetup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "v" => a.successor
local notation "C" => (v).setup
variable (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (active : Expr) (reg : Fin 4→Expr)
local notation "ports" => publicPorts (a:=a) sh floor count hub g Y active reg
local notation:max "banks" w:arg => menu.banks sh floor count hub g Y w
local notation "base" => (v).operandFloor (a.rebased floor)
local notation "cfg" => publicOperands z roots menu.payload
local notation "idx" => menu.publicInputIndex




/-- The old-host correction is the fourth auxiliary column of the same resident row. -/
theorem public_old_host {H K : ℕ} (values : (ports).Values H K)
    (digits : (ports).casts.bits=(C).fallbackBits) (x : ℕ) (h : Fin H) (group : Fin K)
    (small : (values.aux 3 h group).val<2^(ports).casts.bits) :
    ((cfg).oldConfig.header ((cfg).basic
      (menu.publicData sh floor count hub g Y active reg values digits x h group)) 3).val=
      (values.aux 3 h group).val :=by
  apply (menu.public_header_register sh floor count hub g Y active reg values digits x h group 3).trans
  exact Fin.val_cast_of_lt small

/-- Columns zero and one of a true fallback input are the group and fine
coordinates at the donor in its printed row. -/
theorem public_tree_coordinate {H K : ℕ} (values : (ports).Values H K)
    (digits : (ports).casts.bits=(C).fallbackBits) (x : ℕ) (h : Fin H) (group : Fin K)
    (row : Fin (cfg).oldConfig.count) (which : Fin 2)
    (inside : x<2^(ports).coordinates.fine)
    (donorFits : (finProdFinEquiv.symm row : Fin (cfg).donors×Fin (2*(cfg).oldCap)).1.val<
      2^(ports).coordinates.residual)
    (small : (values.coord ⟨which.val,by omega⟩ ⟨x,inside⟩ ⟨_,donorFits⟩ h group).val<2^(ports).casts.bits) :
    ((cfg).oldConfig.digit ((cfg).basic
      (menu.publicData sh floor count hub g Y active reg values digits x h group)) row ⟨which.val,by omega⟩).val=
      (values.coord ⟨which.val,by omega⟩ ⟨x,inside⟩ ⟨_,donorFits⟩ h group).val :=by
  exact menu.public_donor_word sh floor count hub g Y active reg values digits x h group row which
    inside donorFits small

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
