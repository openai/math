import OAI.Computability.BorderVNP.FiniteEvaluatorCellKey
import OAI.Computability.BorderVNP.PackedInheritedMergedOrdinal

/-! # Identifying the real natural-numbered packet with an arbitrarily named field cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Merged.CellKey

open Crossing Packing Packing.Inherited Packing.Inherited.Placement CellSparse
open private padded_lt mem_padded prefix_sum from OAI.Computability.BorderVNP.PackedInheritedMergedOrdinal
open scoped Classical

variable {D ns : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns)

private abbrev Resident := {v : N.Site // cell v=c}
private def slot : Resident N cell c ↪ Fin ns := (Function.Embedding.subtype _).trans siteID

private theorem ordered :
    (orderedSites N cell c siteID).Pairwise (fun x y => siteID x.val < siteID y.val) := by
  let id := slot N cell c siteID
  let _ := LinearOrder.lift' id id.injective
  let fin : Fintype (Resident N cell c) := @Subtype.fintype _ (fun v => cell v=c)
    (fun _ => Classical.propDecidable _) N.finiteSite
  exact (Finset.sortedLT_sort (@Finset.univ _ fin)).pairwise

private theorem prefix_total (state : N.Site → Site) (v : Resident N cell c) :
    boxBase N cell c siteID state v.val = ∑ u : Resident N cell c,
      if siteID u.val < siteID v.val then (state u.val).boxes.length else 0 := by
  let xs := orderedSites N cell c siteID
  rw [boxBase,dite_eq_left v.property,List.length_flatMap]
  have whole : xs.toFinset=Finset.univ := by ext u; simp [xs,orderedSites]
  exact prefix_sum (slot N cell c siteID) xs (Finset.sort_nodup _ _) whole (ordered N cell c siteID)
    (fun u => (state u.val).boxes.length) v (by simp [xs,orderedSites])

variable (code : C ↪ ℕ) (owner : Fin ns → ℕ) (aligned : ∀ v, owner (siteID v)=code (cell v))

include aligned in
/-- Filtering the padded public table returns the original sites in their actual sparse ID order. -/
theorem ordered_public : (orderedSites N cell c siteID).map Subtype.val = FinalCell.sites siteID owner (code c) := by
  let left := (orderedSites N cell c siteID).map Subtype.val
  have hleft : left.Nodup := (Finset.sort_nodup _ _).map Subtype.val_injective
  have perm : left.Perm (FinalCell.sites siteID owner (code c)) :=
    (List.perm_ext_iff_of_nodup hleft (FinalCell.sites_nodup siteID owner _)).2 (by
      intro v
      rw [mem_padded N (fun v => code (cell v)) (code c) siteID owner aligned v,code.injective.eq_iff]
      constructor
      · rintro h
        obtain ⟨u,_,rfl⟩ := List.mem_map.mp h
        exact u.property
      · intro h
        exact List.mem_map.mpr ⟨⟨v,h⟩,by simp [orderedSites],rfl⟩)
  let _ := LinearOrder.lift' siteID siteID.injective
  have a : left.Pairwise (· ≤ ·) := List.pairwise_map.mpr ((ordered N cell c siteID).imp (fun h => le_of_lt h))
  have b : (FinalCell.sites siteID owner (code c)).Pairwise (· ≤ ·) := (padded_lt N (code c) siteID owner).imp (fun h => le_of_lt h)
  exact perm.eq_of_pairwise' a b

include aligned in
/-- The true sparse box ordinal computed in the numeric cell equals the original site's box prefix. -/
theorem first_box (state : N.Site → Site) (v : Resident N cell c) :
    boxBase N cell c siteID state v.val=FinalCell.firstBox siteID owner state v.val := by
  let key := fun u => code (cell u)
  let ev : Resident N cell c ≃ Resident N key (code c) :=
    Equiv.subtypeEquivRight (fun _ => code.injective.eq_iff.symm)
  let vn := ev v
  have h := boxBase_public N key (code c) siteID owner aligned state vn
  have both := (prefix_total N key (code c) siteID state vn).symm.trans h
  refine (prefix_total N cell c siteID state v).trans (Eq.trans ?_ both)
  let term (u : N.Site) := if siteID u < siteID v.val then (state u).boxes.length else 0
  convert! Fintype.sum_equiv ev (fun u => term u.val) (fun u => term u.val) (fun _ => rfl) using 1
  exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)

include aligned in
/-- The complete physically numbered field directory equals the merged mathematical packet
at the original named cell. This includes rebased interval records, private box IDs and every report address. -/
theorem packet_directory [Fintype P] {M np : ℕ} (edgeID : N.Edge ↪ Fin M) (portID : P ↪ Fin np)
    (state : N.Site → Site) (reports : List (List ℕ)) :
    Placement.packet N cell c siteID edgeID portID state reports =
      FinalCell.directory owner N (fun v => code (cell v)) siteID edgeID portID state (code c) reports := by
  let xs := orderedSites N cell c siteID
  have order := ordered_public N cell c siteID code owner aligned
  unfold Placement.packet FinalCell.directory mergedSiteDirectory Directory.mergeSites
  rw [←order,List.flatMap_map,List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro v _
  have box := first_box N cell c siteID code owner aligned state v
  rcases v with ⟨v,hv⟩
  subst c
  unfold siteRows FinalCell.binding
  rw [box,binding_key N cell code siteID edgeID portID state v]
  have slab := site N cell code (cell v) siteID state ⟨v,rfl⟩
  exact congrArg (fun a => (state v).placedRows a (FinalCell.firstBox siteID owner state v) ++
    Placement.ties N cell (cell v) siteID edgeID portID state ⟨v,rfl⟩) slab.symm

end FiniteEvaluator.Merged.CellKey

end BorderVNP
end Computability
end OAI
