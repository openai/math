import OAI.Hierarchy.DescentDatedSignedLaunchTokens

namespace OAI
/-! The source path and source vertex read at a live launch seat come from its single measured parent. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentSharedCableNames
open DescentHaloWalkRAM DescentHaloPackedRebase DescentParallelBase.ParentFilter
open scoped Classical Fin.CommRing
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (c : v.SignedChart)
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "s" => v.signed
local notation "D" => DepotRAM.Shape.degree (v.ticket.depotShape v.short)
variable (hosts : v.material.oldHosts = v.signed.priorHosts)
    (bands : v.material.oldGroups=v.material.groups*v.material.blocks)
    (R : Fin v.material.oldHosts → Fin (v.ticket.depotShape v.short).degree → Option (Fin v.material.oldHosts))
    (state : Fin v.material.oldHosts → Fin v.material.oldGroups → DepotRAM.Parts (v.ticket.depotShape v.short))
local notation "cal" => DepotRAM.Material.reverseEntries (v.ticket.depotShape v.short) R
local notation "rev" => fun h (_ : Fin v.material.oldGroups) => digest (cal h)
variable (bound : ∀h g z, DepotRAM.Material.ParentRoom (v.ticket.depotShape v.short) v.materialFormat (state h g) (digest (DepotRAM.Material.reverseEntries (v.ticket.depotShape v.short) R h)) z
    v.signed.lowSites v.signed.tickets v.signed.cap)
variable (x : Fin v.signed.blocks) (o : Fin v.signed.residentSlots) (h : Fin v.signed.priorHosts) (g : Fin v.signed.groups)
local notation "z" => c.donorSeat o
local notation "u" => Fin.cast hosts.symm h
local notation "lane" => finProdFinEquiv (g,Fin.cast c.blocks x)
local notation "donor" => v.originalParent R state bands bound z u lane
variable (p : Source (breadth (v.ticket.depotShape v.short).degree) v.signed.lowSites v.signed.tickets v.signed.cap)
    (seat : v.originalParent R state bands bound (c.donorSeat o) (Fin.cast hosts.symm h) (finProdFinEquiv (g,Fin.cast c.blocks x))=some p)
    (space : Fused.capacity (v.ticket.depotShape v.short).degree v.signed.lowSites v.signed.tickets v.signed.cap ≤ 2^v.material.fieldBits)

include seat space in
private theorem launch_coordinate (low : Bool) :
    v.launchNumber c hosts bands R state x o low h g = if low then p.src.low.val else p.src.path.val+1 := by
  let f : Fin 9 := if low then 2 else 0
  have readback : DepotRAM.Material.Sheets.fields fmt v.materialFormat state rev (DepotRAM.Material.Sheets.id fmt f z) u
      (Fin.cast bands.symm lane) =
      DepotRAM.Material.parentDigits (((z).1.val*(fmt).cap+(z).2.1.val)*11+(z).2.2.val) donor f := by
    simp only [originalParent, DepotRAM.Material.Sheets.fields,DepotRAM.Material.Sheets.id,DepotRAM.Material.Sheets.fieldId,
      Equiv.symm_apply_apply,DepotRAM.Material.Sheets.allFields,Fin.val_castLE,dite_eq_left f.isLt]
    exact DepotRAM.Material.parent_read fmt v.materialFormat (state u (Fin.cast bands.symm lane)) (digest (cal u))
        z (bound u _ z) f
  unfold launchNumber
  change (DepotRAM.Material.Sheets.fields fmt v.materialFormat state rev
    (DepotRAM.Material.Sheets.id fmt f z) u (Fin.cast bands.symm lane)).val = _
  rw [readback,seat]
  have a:=p.src.path.isLt
  have b:=p.src.low.isLt
  unfold Fused.capacity at space
  cases low
  · change (p.src.path.val+1) % 2^(e).fieldBits=p.src.path.val+1
    exact Nat.mod_eq_of_lt (by omega)
  · change p.src.low.val % 2^(e).fieldBits=p.src.low.val
    exact Nat.mod_eq_of_lt (by omega)

include seat space in
theorem original_forward :
    (v.originalDigits c hosts bands R state).forward x o h g =
      Packed.token (some (Fin.cast (congrArg breadth c.degree.symm) p.src.path)) := by
  apply Fin.ext
  change ((v.launchNumber c hosts bands R state x o false h g : Cell (Packed.bits (s).reach))).val = p.src.path.val+1
  rw [Fin.val_natCast,v.launch_coordinate c hosts bands R state bound x o h g p seat space false]
  apply Nat.mod_eq_of_lt
  change p.src.path.val+1 < 2^(Packed.bits (breadth (s).degree))
  rw [c.degree]
  exact (Nat.succ_lt_succ p.src.path.isLt).trans_le (Nat.le_pow_clog (by decide) _)

include seat space in
theorem original_low :
    ((v.originalDigits c hosts bands R state).low x o h g).val=p.src.low.val := by
  change ((v.launchNumber c hosts bands R state x o true h g : Cell (Packed.bits (s).lowSites))).val = _
  rw [Fin.val_natCast,v.launch_coordinate c hosts bands R state bound x o h g p seat space true]
  exact Nat.mod_eq_of_lt (p.src.low.isLt.trans_le ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
