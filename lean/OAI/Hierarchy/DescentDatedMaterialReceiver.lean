import OAI.Hierarchy.DescentDatedMaterialSockets
import OAI.Hierarchy.DescentOrdinaryMaterialRaw

namespace OAI
/-! The causal previous packed depot and prior rotor determine the whole incoming signed-parent record. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentHaloWalkRAM DescentSharedCableNames DescentHaloPackedRebase DescentParallelBase.ParentFilter
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DepotRAM.Material.Route
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "H" => v.material.oldHosts
local notation "P₀" => breadth (DepotRAM.Shape.degree (v.ticket.depotShape v.short))
local notation "b" => v.material.fieldBits
local notation "B" => v.material.blocks
local notation "G₁" => v.material.groups
local notation "Q" => v.signed.lowSites
local notation "K" => v.signed.tickets
local notation "L" => v.signed.cap
variable (R : Fin v.material.oldHosts→Fin (v.ticket.depotShape v.short).degree→Option (Fin v.material.oldHosts))
    (state : Fin v.material.oldHosts→Fin v.material.oldGroups→DepotRAM.Parts (v.ticket.depotShape v.short))
    (bands : v.material.oldGroups=v.material.groups*v.material.blocks)
    (room : Fused.capacity (v.ticket.depotShape v.short).degree v.signed.lowSites v.signed.tickets v.signed.cap≤2^v.material.fieldBits)
    (pitch : 0<v.materialPitch) (budget : v.materialPitch≤v.signed.lowSites)
local notation "cal" => DepotRAM.Material.reverseEntries fmt R
local notation "rev" => fun h (_:Fin v.material.oldGroups)=>digest (cal h)
variable (bound : ∀h g z,DepotRAM.Material.ParentRoom (v.ticket.depotShape v.short) v.materialFormat (state h g) (digest (DepotRAM.Material.reverseEntries (v.ticket.depotShape v.short) R h)) z v.signed.lowSites v.signed.tickets v.signed.cap)

def originalParent (z : DepotRAM.Material.Seat fmt) (h : Fin H) (g : Fin (G₁*B)) :=
  DepotRAM.Material.parent fmt v.materialFormat (state h (Fin.cast bands.symm g)) (digest (cal h)) z (bound h _ z)
local notation "parents" => v.originalParent R state bands bound
def incoming (p : Fin P₀) (z : DepotRAM.Material.Seat fmt) (x : Fin B) (h : Fin (e).hosts) (g : Fin G₁) :=
  fromDonor R v.materialPitch pitch budget room p x (parents z) h g

theorem actual_socket (p : Fin P₀) (z : DepotRAM.Material.Seat fmt) (x : Fin B) (f : Port) :
    v.socketValue R state bands p z x f=
      (fun h g=>atPort R (v.incoming R state bands room pitch budget bound p z x h g) f) :=by
  funext h g
  let low := (z.1.val*(fmt).cap+z.2.1.val)*11+z.2.2.val
  have original (old : Fin H) (i : Fin (G₁*B)) :
      DepotRAM.Material.Sheets.fields fmt v.materialFormat state rev
        (DepotRAM.Material.Sheets.id fmt (donorField f) z) old (Fin.cast bands.symm i)
      =DepotRAM.Material.parentDigits low (parents z old i) (donorField f) :=by
    simp only [DepotRAM.Material.Sheets.fields,DepotRAM.Material.Sheets.id,DepotRAM.Material.Sheets.fieldId,
      Equiv.symm_apply_apply,DepotRAM.Material.Sheets.allFields,Fin.val_castLE,dite_eq_left (donorField f).isLt]
    exact DepotRAM.Material.parent_read fmt v.materialFormat (state old (Fin.cast bands.symm i)) (digest (cal old))
        z (bound old _ z) (donorField f)
  unfold socketValue
  simp only [original]
  exact from_original R v.materialPitch pitch budget room p x (parents z) low h g f

theorem incoming_location (p : Fin P₀) (z : DepotRAM.Material.Seat fmt) (x : Fin B) (h : Fin (e).hosts)
    (g : Fin G₁) {r : Fused.Raw R Q K L b} (hit : v.incoming R state bands room pitch budget bound p z x h g=some r) :
    receiver H v.materialPitch h=some r.receiver.1 ∧ Gather.select (Gather.reaching R) r.receiver.1 r.path=some r.host :=
  from_original_location R v.materialPitch pitch budget room p x (parents z) h g hit

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
