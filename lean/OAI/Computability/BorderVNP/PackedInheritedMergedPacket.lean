import OAI.Computability.BorderVNP.PackedInheritedMergeRows
import OAI.Computability.BorderVNP.PackedInheritedPlacementBoxes

/-! # Field read of the fully merged site packet at its actual physical assignment

Sites are sorted by sparse public site ID. Their one-copy lists are concatenated
in that order; each site's first box is exactly the length of the preceding
lists. The packet contains the physical records and compressed incidence ties.
A finite-field power scan against its genuine reported bits therefore reads the
product of the true local field factors for this assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Placement

open CellSparse CellAddresses Crossing
open scoped Classical

variable {D M np ns : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
    {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin M)
    (portID : P ↪ Fin np) (state : N.Site → Site)

private abbrev Owned := {v : N.Site // cell v = c}

/-- Owned fine sites in ascending sparse row-ID order. -/
noncomputable def orderedSites : List (Owned N cell c) :=
  let id : Owned N cell c ↪ Fin ns := (Function.Embedding.subtype _).trans siteID
  let _ := LinearOrder.lift' id id.injective
  Finset.univ.sort

private theorem allSites (v : Owned N cell c) : v ∈ orderedSites N cell c siteID := by
  simp [orderedSites]

/-- The box table actually stored for this cell. -/
noncomputable def cellBoxes := (orderedSites N cell c siteID).flatMap (fun u => (state u.val).boxes)

/-- First box ordinal of a fine site in the merged cell. -/
noncomputable def boxBase (v : N.Site) : ℕ :=
  let sites := orderedSites N cell c siteID
  if h : cell v = c then ((sites.take (sites.idxOf ⟨v,h⟩)).flatMap (fun u => (state u.val).boxes)).length else 0

private theorem boxes_split (v : Owned N cell c) :
    ∃ pre post : List (List Factor), pre.length = boxBase N cell c siteID state v.val ∧
      cellBoxes N cell c siteID state = pre ++ (state v.val).boxes ++ post := by
  let vs := orderedSites N cell c siteID
  let j := vs.idxOf v
  have hj : j < vs.length := List.idxOf_lt_length_iff.mpr (allSites N cell c siteID v)
  let fs := fun u : Owned N cell c => (state u.val).boxes
  refine ⟨(vs.take j).flatMap fs,(vs.drop (j+1)).flatMap fs,?_,?_⟩
  · rw [boxBase,dite_eq_left v.property]
  · have eq := List.take_append_drop j vs
    rw [List.drop_eq_getElem_cons hj,show vs[j] = v from List.getElem_idxOf hj] at eq
    change vs.flatMap fs = (vs.take j).flatMap fs ++ fs v ++ (vs.drop (j+1)).flatMap fs
    simpa only [List.flatMap_append,List.flatMap_cons,List.append_assoc] using (congrArg (List.flatMap fs) eq.symm)

/-- Every locally stored box ordinal lies inside the physical cell table. -/
theorem boxBase_fits (v : Owned N cell c) :
    boxBase N cell c siteID state v.val + (state v.val).boxes.length ≤ (cellBoxes N cell c siteID state).length := by
  obtain ⟨pre,post,h,eq⟩ := boxes_split N cell c siteID state v
  rw [←h,eq,List.length_append,List.length_append]
  omega

/-- Reading an actual rebased ordinal retrieves its original private table bytes. -/
theorem boxBase_read (v : Owned N cell c) (j : ℕ) (hj : j < (state v.val).boxes.length) :
    (cellBoxes N cell c siteID state).getD (boxBase N cell c siteID state v.val+j) [] = (state v.val).boxes.getD j [] := by
  obtain ⟨pre,post,h,eq⟩ := boxes_split N cell c siteID state v
  rw [←h,eq,List.append_assoc,List.getD_append_right _ _ _ _ (Nat.le_add_right ..),Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hj]

variable [Fintype P]

/-- The concrete per-cell directory containing all live site rows, one-copy boxes and report addresses. -/
noncomputable def packet (reports : List (List ℕ)) : Directory :=
  Directory.mergeSites (orderedSites N cell c siteID) (fun v => (state v.val).boxes)
    (siteRows N cell c siteID edgeID portID state (boxBase N cell c siteID state)) reports

variable (hs : ∀ v, (state v).incoming = incoming N v) (loc : ∀ v, (state v).Local)
    (schema : ∀ v, (state v).Schema) (relative : ∀ v, (state v).RelativeBoxes)
    {K : Type*} [Field K] [Fintype K]
    (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c (fun v => (state v).size)) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool)

private noncomputable abbrev full (tail : List Bool) := lookup (bank N cell c (fun v => (state v).size) g a x ++ tail)

include hs loc schema relative in
/-- The emitted packet, with arbitrary trailing report operands, reads the true product
of physical site contributions exactly when the aggregate count bits match. -/
theorem checked_packet (reports : List (List ℕ)) (values : Fin reports.length → K) (tail : List Bool) :
    let D := packet N cell c siteID edgeID portID state reports
    let b := full N cell c state g a x tail
    MergeField.checked D b values = if MergeField.Matches D b then
      ∏ v : Owned N cell c, siteFactor N cell c siteID edgeID portID state (fun _ => fieldWeight (FieldPowers.entry values))
        (cellBoxes N cell c siteID state) (boxBase N cell c siteID state) g x v a else 0 := by
  dsimp only
  let sites := orderedSites N cell c siteID
  let base := boxBase N cell c siteID state
  let merged := cellBoxes N cell c siteID state
  let val := FieldPowers.entry values
  let fac := fun v : Owned N cell c => siteFactor N cell c siteID edgeID portID state (fun _ => fieldWeight val) merged base g x v a
  have eq := MergeField.checked_merge sites (fun v => (state v.val).boxes)
    (siteRows N cell c siteID edgeID portID state base) reports (full N cell c state g a x tail) values
  refine eq.trans (if_congr Iff.rfl ?_ rfl)
  have parts : (sites.map (fun v => MergeField.guarded val
        ⟨merged,siteRows N cell c siteID edgeID portID state base v,[]⟩ (full N cell c state g a x tail))).prod =
      (sites.map fac).prod := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro v _
    exact guarded_siteRows N cell c siteID edgeID portID state hs g a x val merged base loc
      (fun u r hr => (schema u r hr).1) (boxBase_fits N cell c siteID state) (boxBase_read N cell c siteID state)
      (fun u => (relative u.val).reachable _) v tail
  refine parts.trans ?_
  have nodup : sites.Nodup := by apply Finset.sort_nodup
  have whole : sites.toFinset = Finset.univ := by apply Finset.sort_toFinset
  exact (List.prod_toFinset fac nodup).symm.trans (congrArg (Finset.prod · fac) whole)

include hs loc schema relative in
/-- At the uniquely installed physical staging tape, the actual packet reads all earlier
private choices, preserving each rejection, sign and paid-entry value in the merged product. -/
theorem checked_install (reports : List (List ℕ)) (values : Fin reports.length → K) (tail : List Bool)
    (work : Work N cell c state) :
    let D := packet N cell c siteID edgeID portID state reports
    let a := install N cell c siteID edgeID portID state hs g x work
    let b := full N cell c state g a x tail
    MergeField.checked D b values = if MergeField.Matches D b then
      ∏ v : Owned N cell c, ((state v.val).observe (Inherited.bits (work v)
        (canonical N cell c edgeID portID v g x ∘ Fin.cast (hs v.val)))).elim 0 (fieldWeight (FieldPowers.entry values))
      else 0 := by
  dsimp only
  let a := install N cell c siteID edgeID portID state hs g x work
  let val := FieldPowers.entry values
  refine (checked_packet N cell c siteID edgeID portID state hs loc schema relative g a x reports values tail).trans
    (if_congr Iff.rfl (Finset.prod_congr rfl (fun v _ => ?_)) rfl)
  exact siteFactor_install N cell c siteID edgeID portID state hs g x (fun _ => fieldWeight val)
    (cellBoxes N cell c siteID state) (boxBase N cell c siteID state) loc (fun u r hr => (schema u r hr).1)
    (boxBase_fits N cell c siteID state) (boxBase_read N cell c siteID state)
    (fun u => (relative u.val).reachable _) work v

include hs loc schema relative in
/-- Every full slab tape outside the unique installed image contributes zero, for
arbitrary declared count words and even when its private factor reads succeed. -/
theorem checked_uninstalled (reports : List (List ℕ)) (values : Fin reports.length → K) (tail : List Bool)
    (bad : install N cell c siteID edgeID portID state hs g x (extract N cell c siteID state a) ≠ a) :
    MergeField.checked (packet N cell c siteID edgeID portID state reports) (full N cell c state g a x tail) values = 0 := by
  have missing := mt (install_iff N cell c siteID edgeID portID state hs g x (cellBoxes N cell c siteID state) a).mp bad
  obtain ⟨v,hv⟩ := not_forall.mp missing
  rw [checked_packet N cell c siteID edgeID portID state hs loc schema relative g a x reports values tail]
  split
  · apply Finset.prod_eq_zero (Finset.mem_univ v)
    unfold siteFactor
    rw [ite_eq_right hv]
  · rfl

end Packing.Inherited.Placement

end BorderVNP
end Computability
end OAI
