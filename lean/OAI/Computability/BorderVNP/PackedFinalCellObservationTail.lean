import OAI.Computability.BorderVNP.CellGuardedObservations
import OAI.Computability.BorderVNP.PackedInheritedMergeRows
import OAI.Computability.BorderVNP.PackedFinalCellFields
import OAI.Computability.BorderVNP.PackedInheritedPlacementBoxes

/-! # The original signed observation list is independent of the guessed report tail -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Placement

open CellSparse CellAddresses Crossing
open scoped Classical
open private region sizes off off_fits read_prefix tie_read rows_observations from OAI.Computability.BorderVNP.PackedInheritedMergeRows

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin M)
    (portID : P ↪ Fin np) (state : N.Site → Site)
    (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c (sizes N state)) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool)

private theorem site_checked (merged : List (List Factor)) (base : N.Site → ℕ)
    (v : {v : N.Site // cell v=c}) (bank : ℕ → Bool) :
    (⟨merged,siteRows N cell c siteID edgeID portID state base v,[]⟩ : Directory).guardedObservations bank =
      if ∀ r ∈ ties N cell c siteID edgeID portID state v, r.Valid merged bank then
        (state v.val).placedObserve merged (off N cell c siteID state v) (base v.val) bank else none := by
  rw [Directory.guardedObservations,rows_observations]
  unfold Site.placedObserve
  simp only [siteRows,List.forall_mem_append,Site.placedDirectory]
  split_ifs <;> simp_all
  symm
  apply ite_eq_right
  intro hg
  exfalso
  have hn : ¬ ∀ r ∈ (state v.val).placedRows (off N cell c siteID state v) (base v.val), r.Valid merged bank := by
    push Not
    assumption
  exact hn hg

/-- The original ordered signed/gadget observations and all site checks
persist across *any* trailing binary reports, even malformed ones. -/
theorem checked_site_tail (merged : List (List Factor)) (base : N.Site → ℕ)
    (hs : ∀ v, (state v).incoming=incoming N v) (v : {v : N.Site // cell v=c})
    (locality : (state v.val).Local) (fit : ∀ r ∈ (state v.val).rows, r.BoxRefFits (state v.val).boxes.length)
    (span : base v.val+(state v.val).boxes.length ≤ merged.length)
    (get : ∀ j < (state v.val).boxes.length, merged.getD (base v.val+j) [] = (state v.val).boxes.getD j [])
    (relative : (state v.val).RelativeBoxes) (tail : List Bool) :
    let dir := (⟨merged,siteRows N cell c siteID edgeID portID state base v,[]⟩ : Directory)
    let pre := region N cell c state g a x
    dir.guardedObservations (lookup (pre++tail)) = dir.guardedObservations (lookup pre) := by
  dsimp only
  let pre := region N cell c state g a x
  let shift := off N cell c siteID state v
  have ht : (∀ r ∈ ties N cell c siteID edgeID portID state v, r.Valid merged (lookup (pre++tail))) ↔
      ∀ r ∈ ties N cell c siteID edgeID portID state v, r.Valid merged (lookup pre) := by
    simp only [ties,List.forall_mem_map]
    exact forall_congr' fun r => imp_congr_right fun _ =>
      tie_read N cell c siteID edgeID portID state hs g a x v r merged tail
  rw [site_checked,site_checked]
  apply if_congr ht _ rfl
  rw [(state v.val).placed_observe merged shift (base v.val) fit span get (relative.reachable shift),
      (state v.val).placed_observe merged shift (base v.val) fit span get (relative.reachable shift)]
  apply locality
  intro j hj
  exact read_prefix N cell c state g a x tail _ ((Nat.add_lt_add_left hj shift).trans_le (off_fits N cell c siteID state v))

end Packing.Inherited.Placement

namespace Packing.Inherited.FinalCell

open CellSparse CellAddresses Crossing BankBoxOrdinal
open scoped Classical
open private entries before_length split_table from OAI.Computability.BorderVNP.PackedBankBoxOrdinal
open private slot_live off from OAI.Computability.BorderVNP.PackedBankSortedCell
open private region from OAI.Computability.BorderVNP.PackedInheritedMergeRows

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → ℕ) (c : ℕ) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin M)
    (portID : P ↪ Fin np) (owner : Fin ns → ℕ) (state : N.Site → Site)

omit [Fintype P] in
private theorem firstBox_span {v : N.Site} (hv : v ∈ sites siteID owner c) :
    firstBox siteID owner state v + (state v).boxes.length ≤
      ((sites siteID owner c).flatMap fun u => (state u).boxes).length := by
  let bs := slots siteID fun u => (state u).boxes
  rw [← sorted_fragments siteID owner (fun u => (state u).boxes) c,← site_owner siteID owner hv]
  change _ ≤ (table owner bs (owner (siteID v))).length
  rw [split_table,List.length_append,List.length_append,before_length]
  have live : bs (siteID v) = (state v).boxes := slot_live siteID _ v
  rw [live]
  exact Nat.add_le_add_left (Nat.le_add_right _ _) _

/-- All passing site wiring and actual gadget row identities are fixed before
the all-team report guesses. The proof uses the selected stable box ordinals
and the true finite region occupied by every retained site and endpoint. -/
theorem guarded_tail (reports : List (List ℕ)) (ho : ∀ v, owner (siteID v)=cell v)
    (hin : ∀ v, (state v).incoming=incoming N v) (schema : ∀ v, (state v).Schema)
    (locality : ∀ v, (state v).Local) (relative : ∀ v, (state v).RelativeBoxes)
    (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c (fun v => (state v).size)) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) (tail : List Bool) :
    let dir := directory owner N cell siteID edgeID portID state c reports
    let pre := region N cell c state g a x
    dir.guardedObservations (lookup (pre++tail)) = dir.guardedObservations (lookup pre) := by
  dsimp only
  let live := sites siteID owner c
  let merged := live.flatMap fun v => (state v).boxes
  let base := firstBox siteID owner state
  let rs := fun v => (state v).placedRows (off N cell siteID state v) (base v) ++ binding N cell siteID edgeID portID state v
  apply Directory.flatMap_guarded_congr live merged rs
  intro v hv
  have eq := (ho v).symm.trans (site_owner siteID owner hv)
  let vv : {v : N.Site // cell v=c} := ⟨v,eq⟩
  have h := Placement.checked_site_tail N cell c siteID edgeID portID state g a x merged base hin vv
    (locality v) (fun r hr => (schema v r hr).1) (firstBox_span N c siteID owner state hv)
    (fun _ hi => box_get siteID owner state hv _ hi) (relative v) tail
  subst c
  exact h

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
