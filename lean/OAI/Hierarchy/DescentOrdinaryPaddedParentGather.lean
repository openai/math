import OAI.Hierarchy.DescentOrdinaryPaddedWalk
import OAI.Hierarchy.DescentDatedSignedHome
import OAI.Hierarchy.DescentOrdinaryMaterialShelf

namespace OAI
/-! An unoccupied normalized host can receive no parent from a genuine old donor. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentHaloWalkRAM DescentSharedCableNames DescentRawCablePanel.DepotRAM.Material.Route
open scoped Classical
variable {H D n : ℕ} (R:Fin H→Fin D→Option (Fin H))
theorem padded_receiver {J U : Type} [Fintype J] [DecidableEq J] [DecidableEq U] [Fintype U] {K groups k pitch : ℕ}
    (group:J≃Fin groups) (host:U≃Fin (Fintype.card U)) (fits:Fintype.card U≤K)
    (count:Fintype.card U=n*pitch) (positive:0<pitch)
    (x:Fin (2^k)) (h:Fin K) (g:Fin groups)
    (hole:wholeHost group.toEmbedding (host.toEmbedding.trans (Fin.castLEEmb fits)) x h g=none)
    {v:Fin H} (back:receiver H pitch h=some v) : n≤v.val:=by
  have big : Fintype.card U≤h.val:=by
    by_contra! sm
    let u:=host.symm ⟨h.val,sm⟩
    let row : Stage.Host J U k:=((group.symm g,u),x)
    have hit:= (wholeHost_iff group.toEmbedding (host.toEmbedding.trans (Fin.castLEEmb fits)) x h g row).2
      ⟨group.apply_symm_apply g,Fin.ext (by simp [row,u]),rfl⟩
    rw [hole] at hit;contradiction
  have div : h.val/pitch=v.val:=by unfold receiver at back;split at back;exact (congrArg Fin.val (Option.some.inj back));contradiction
  rw [←div,Nat.le_div_iff_mul_le positive,←count]
  exact big
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
