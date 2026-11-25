import OAI.Computability.BorderVNP.PackedInheritedMergedPacket
import OAI.Computability.BorderVNP.PackedBankSortedCell

/-! # The checked merged packet is the actual sparse owner-sorted cell directory

The public scan works on padded site slots. Empty slots contain no boxes or
rows. Filtering the owner slots and decoding occupied IDs gives the same
order as sorting the true owned sites. The scanned box prefix is the length
of the original site's preceding one-copy fragments in this order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Placement

open Crossing CellSparse
open scoped Classical

variable {D ns : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → ℕ) (c : ℕ)
    (siteID : N.Site ↪ Fin ns) (owner : Fin ns → ℕ) (aligned : ∀ v, owner (siteID v) = cell v)

private abbrev Owned := {v : N.Site // cell v = c}

private def name : Owned N cell c ↪ Fin ns := (Function.Embedding.subtype _).trans siteID

private theorem ordered_lt :
    (orderedSites N cell c siteID).Pairwise (fun u v => siteID u.val < siteID v.val) := by
  let _ := LinearOrder.lift' (name N cell c siteID) (name N cell c siteID).injective
  let fin : Fintype (Owned N cell c) := @Subtype.fintype _ (fun v => cell v = c) (fun _ => Classical.propDecidable _) N.finiteSite
  exact (Finset.sortedLT_sort (@Finset.univ _ fin)).pairwise

private theorem padded_lt : (FinalCell.sites siteID owner c).Pairwise (fun u v => siteID u < siteID v) := by
  apply List.Pairwise.filterMap (Function.partialInv siteID) _
    ((List.pairwise_lt_finRange ns).filter (fun i => decide (owner i = c)))
  intro i j hij u hu v hv
  have hi := (siteID.injective.isPartialInv u i).mp hu
  have hj := (siteID.injective.isPartialInv v j).mp hv
  simpa only [hi,hj] using hij

include aligned in
private theorem mem_padded (v : N.Site) : v ∈ FinalCell.sites siteID owner c ↔ cell v = c := by
  constructor
  · exact fun hv => (aligned v).symm.trans (FinalCell.site_owner siteID owner hv)
  · intro hv
    refine List.mem_filterMap.mpr ⟨siteID v,List.mem_filter.mpr ⟨List.mem_finRange _,?_⟩,
      Function.partialInv_left siteID.injective v⟩
    simp [aligned v,hv]

include aligned in
/-- The ID-ordered real-site list agrees with the actual padded slot filter and decoder. -/
theorem orderedSites_public : (orderedSites N cell c siteID).map Subtype.val = FinalCell.sites siteID owner c := by
  let left := (orderedSites N cell c siteID).map Subtype.val
  have hl : left.Nodup := (Finset.sort_nodup _ _).map Subtype.val_injective
  have perm : left.Perm (FinalCell.sites siteID owner c) := (List.perm_ext_iff_of_nodup hl (FinalCell.sites_nodup siteID owner c)).2 (by
    intro v
    rw [mem_padded N cell c siteID owner aligned v]
    constructor
    · rintro hv
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
      exact u.property
    · intro hv
      exact List.mem_map.mpr ⟨⟨v,hv⟩,by simp [orderedSites],rfl⟩)
  let _ := LinearOrder.lift' siteID siteID.injective
  have hs₁ : left.Pairwise (· ≤ ·) := List.pairwise_map.mpr ((ordered_lt N cell c siteID).imp (fun h => le_of_lt h))
  have hs₂ : (FinalCell.sites siteID owner c).Pairwise (· ≤ ·) := (padded_lt N c siteID owner).imp (fun h => le_of_lt h)
  exact perm.eq_of_pairwise' hs₁ hs₂

private theorem prefix_sum {A : Type*} [Fintype A] [DecidableEq A] [BEq A] [LawfulBEq A] (row : A → Fin ns) (xs : List A)
    (nodup : xs.Nodup) (whole : xs.toFinset = Finset.univ) (sorted : xs.Pairwise (fun x y => row x < row y))
    (f : A → ℕ) (v : A) (hv : v ∈ xs) :
    ((xs.take (xs.idxOf v)).map f).sum = ∑ u : A, if row u < row v then f u else 0 := by
  let j := xs.idxOf v
  let pre := xs.take j
  let post := xs.drop (j+1)
  have hj : j < xs.length := List.idxOf_lt_length_iff.mpr hv
  have split : pre ++ v :: post = xs := by
    have h := List.take_append_drop j xs
    rw [List.drop_eq_getElem_cons hj,show xs[j] = v from List.getElem_idxOf hj] at h
    exact h
  have hs := List.pairwise_append.mp (split.symm ▸ sorted)
  have hp (x : A) (hx : x ∈ pre) : row x < row v := hs.2.2 x hx v List.mem_cons_self
  have hq (x : A) (hx : x ∈ post) : ¬row x < row v := lt_asymm ((List.pairwise_cons.mp hs.2.1).1 x hx)
  let val := fun x => if row x < row v then f x else 0
  have prior : pre.map val = pre.map f := List.map_congr_left (fun x hx => ite_eq_left (hp x hx))
  have later : post.map val = post.map (fun _ => 0) := List.map_congr_left (fun x hx => ite_eq_right (hq x hx))
  have total := List.sum_toFinset val nodup
  rw [whole] at total
  change (pre.map f).sum = ∑ u : A, val u
  rw [total,← split,List.map_append,List.sum_append,prior,List.map_cons,List.sum_cons,later]
  simp [val]

variable (state : N.Site → Site)

include aligned in
/-- The public segmented first-box scan computes the precise prefix used by the checked packet. -/
theorem boxBase_public (v : Owned N cell c) :
    boxBase N cell c siteID state v.val = FinalCell.firstBox siteID owner state v.val := by
  let xs := orderedSites N cell c siteID
  let data := fun u : Owned N cell c => (state u.val).boxes.length
  have h₁ : boxBase N cell c siteID state v.val =
      ∑ u : Owned N cell c, if siteID u.val < siteID v.val then data u else 0 := by
    rw [boxBase,dite_eq_left v.property,List.length_flatMap]
    have whole : xs.toFinset = Finset.univ := by ext u; simp [xs,orderedSites]
    exact prefix_sum (name N cell c siteID) xs (Finset.sort_nodup _ _) whole
      (ordered_lt N cell c siteID) data v (by simp [xs,orderedSites])
  refine h₁.trans ?_
  let slot := name N cell c siteID
  unfold FinalCell.firstBox BankBoxOrdinal.base
  apply Fintype.sum_of_injective slot slot.injective
  · intro t ht
    by_cases ho : owner t = owner (siteID v.val)
    · have hnone : Function.partialInv siteID t = none := by
        cases he : Function.partialInv siteID t with
        | none => rfl
        | some u =>
          have hu := (siteID.injective.isPartialInv u t).mp he
          have owned : cell u = c := (aligned u).symm.trans ((congrArg owner hu).trans (ho.trans ((aligned _).trans v.property)))
          exact False.elim (ht ⟨⟨u,owned⟩,hu⟩)
      simp [FinalCell.slots,hnone]
    · simp [ho]
  · intro u
    have ho : owner (slot u) = owner (siteID v.val) := (aligned _).trans (u.property.trans (v.property.symm.trans (aligned _).symm))
    have hv : FinalCell.slots siteID (fun t => (state t).boxes) (slot u) = (state u.val).boxes := by
      change (Function.partialInv siteID (siteID u.val)).elim [] _ = _
      rw [Function.partialInv_left siteID.injective]
      rfl
    simp only [ho,true_and,hv]
    rfl

include aligned in
/-- The real sorted owner packet checked on arbitrary assignments is the final public directory. -/
theorem packet_public [Fintype P] {M np : ℕ} (edgeID : N.Edge ↪ Fin M) (portID : P ↪ Fin np)
    (reports : List (List ℕ)) :
    packet N cell c siteID edgeID portID state reports =
      FinalCell.directory owner N cell siteID edgeID portID state c reports := by
  let xs := orderedSites N cell c siteID
  have hs := orderedSites_public N cell c siteID owner aligned
  unfold packet FinalCell.directory mergedSiteDirectory Directory.mergeSites
  rw [←hs,List.flatMap_map,List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro v _
  have hb := boxBase_public N cell c siteID owner aligned state v
  rcases v with ⟨v,hv⟩
  subst c
  unfold siteRows FinalCell.binding
  rw [hb]

end Packing.Inherited.Placement

end BorderVNP
end Computability
end OAI
