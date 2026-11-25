import OAI.Hierarchy.DescentDatedSignedOriginalLaunch
import OAI.Hierarchy.DescentOrdinaryMaterialParentRoom

namespace OAI
/-! Every forward digit emitted by the ordinary donor is a decodable path or the empty token. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony
open DescentSharedCableNames DescentHaloWalkRAM DescentHaloPackedRebase
open scoped Classical Fin.CommRing
noncomputable section

private theorem token_of_bound {n : ℕ} (x : Cell (Packed.bits n)) (bound : x.val ≤ n) :
    Packed.token (Packed.readToken n x) = x := by
  by_cases live : 0 < x.val
  · rw [Packed.readToken, dite_eq_left ⟨live,bound⟩]
    apply Fin.ext
    change x.val-1+1=x.val
    omega
  · rw [Packed.readToken, dite_eq_right (fun h=>live h.1)]
    apply Fin.ext
    change 0=x.val
    omega

private theorem field_zero (shape : DepotRAM.Shape) (u : DepotRAM.Material.Setup)
    {H G : ℕ} (state : Fin H → Fin G → DepotRAM.Parts shape)
    (reverse_ : Fin H → Fin G → Cell (DepotRAM.chartBits shape))
    (seat : DepotRAM.Material.Seat shape) (h : Fin H) (g : Fin G) :
    (DepotRAM.Material.Sheets.fields shape u state reverse_ (DepotRAM.Material.Sheets.id shape 0 seat) h g).val ≤
      breadth shape.degree := by
  have measured : DepotRAM.Material.Sheets.fields shape u state reverse_
      (DepotRAM.Material.Sheets.id shape 0 seat) h g =
      (DepotRAM.Material.observations shape u (state h g) seat 0 : Cell u.fieldBits) := by
    simp only [DepotRAM.Material.Sheets.fields, DepotRAM.Material.Sheets.id, DepotRAM.Material.Sheets.fieldId,
      Equiv.symm_apply_apply]; rfl
  rw [measured, Fin.val_natCast]
  exact (Nat.mod_le _ _).trans (DepotRAM.Material.previous_paths shape u (state h g) seat).1

theorem original_tokens {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (c : v.SignedChart)
    (hosts : v.material.oldHosts = v.signed.priorHosts)
    (bands : v.material.oldGroups = v.material.groups*v.material.blocks)
    (R : Fin v.material.oldHosts → Fin (v.ticket.depotShape v.short).degree → Option (Fin v.material.oldHosts))
    (state : Fin v.material.oldHosts → Fin v.material.oldGroups → DepotRAM.Parts (v.ticket.depotShape v.short))
    (x o h g) :
    Packed.token (Packed.readToken v.signed.reach ((v.originalDigits c hosts bands R state).forward x o h g)) =
      (v.originalDigits c hosts bands R state).forward x o h g := by
  apply token_of_bound
  change ((v.launchNumber c hosts bands R state x o false h g : Cell (Packed.bits v.signed.reach))).val ≤ _
  rw [Fin.val_natCast]
  apply (Nat.mod_le _ _).trans
  unfold SignedExtent.reach
  rw [c.degree]
  exact field_zero _ _ _ _ _ _ _

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
