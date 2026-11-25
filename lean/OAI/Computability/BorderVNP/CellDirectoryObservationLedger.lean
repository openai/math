import OAI.Computability.BorderVNP.CellDirectoryMerge
import OAI.Computability.BorderVNP.CellDirectoryBoxRebase
import OAI.Computability.BorderVNP.DiagonalTallyCellOperands

/-! # The observation ledger of the merged cell directory

The actual private box sweeps concatenate the ordered observations of every site
in the cell. Relocating a site's box ordinals preserves these observations. Once the
merged checker passes, each externally supplied gadget count is therefore exactly
the sum of the individual site ID frequencies.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open DiagonalTallyMaterialize

variable {ι : Type*}

/-- The occurrences of the merged private directory, in their actual sweep order.
Each site's rows are interpreted against the same final box table. -/
theorem Directory.mergeSites_occurrences (sites : List ι) (tables : ι → List (List Factor))
    (rows : ι → List Record) (reports : List (List ℕ)) :
    (Directory.mergeSites sites tables rows reports).occurrences =
      sites.flatMap (fun i => (⟨sites.flatMap tables,rows i,[]⟩ : Directory).occurrences) := by
  unfold mergeSites occurrences
  simp only [List.flatMap_assoc]

/-- Rebased records retain their site-local observation sequence on the actual
physical bank, including the choice of a zero-valued gadget ID. -/
theorem Directory.observations_rebased (D : Directory) (merged : List (List Factor)) (offset : ℕ)
    (bank : ℕ → Bool) (fit : ∀ r ∈ D.records, r.BoxRefFits D.boxes.length)
    (get : ∀ i < D.boxes.length, merged.getD (offset+i) [] = D.boxes.getD i []) :
    (D.rebaseBoxes merged offset).observations bank = D.observations bank := by
  unfold observations
  rw [← Directory.blocks_visits,← D.blocks_visits,D.blocks_rebaseBoxes_of_getD merged offset fit get]

private theorem observe_flatMap (sites : List ι) (localDir : ι → Directory) (bank : ℕ → Bool)
    (obs : ι → List (Bool × Option ℕ))
    (read : ∀ i ∈ sites, (localDir i).observations bank = some (obs i)) :
    (sites.flatMap (fun i => (localDir i).occurrences)).mapM
        (fun o => o.factor.observe bank o.offset o.copy) = some (sites.flatMap obs) := by
  induction sites with
  | nil => rfl
  | cons i xs ih =>
    have head := read i (by simp)
    have tail := ih (fun j hj => read j (by simp [hj]))
    change (localDir i).occurrences.mapM _ = some (obs i) at head
    simp [List.flatMap_cons,List.mapM_append,head,tail]

/-- The merged checker reads the original site observations once each, in the
stable site ordering used to place its box references. -/
theorem Directory.mergeSites_observations (sites : List ι) (source : ι → Directory) (offset : ι → ℕ)
    (reports : List (List ℕ)) (bank : ℕ → Bool) (obs : ι → List (Bool × Option ℕ))
    (fit : ∀ i ∈ sites, ∀ r ∈ (source i).records, r.BoxRefFits (source i).boxes.length)
    (get : ∀ i ∈ sites, ∀ k < (source i).boxes.length,
      (sites.flatMap fun j => (source j).boxes).getD (offset i+k) [] = (source i).boxes.getD k [])
    (read : ∀ i ∈ sites, (source i).observations bank = some (obs i)) :
    let tables := fun i => (source i).boxes
    let rows := fun i => (source i).records.map (Record.rebaseBox (offset i))
    (mergeSites sites tables rows reports).observations bank = some (sites.flatMap obs) := by
  intro tables rows
  unfold observations
  rw [mergeSites_occurrences]
  apply observe_flatMap
  intro i hi
  exact ((source i).observations_rebased _ (offset i) bank (fit i hi) (get i hi)).trans (read i hi)

/-- Count one fixed gadget ID in the concatenated observations of a complete cell. -/
theorem count_site_ids (sites : List ι) (obs : ι → List (Bool × Option ℕ)) (g : ℕ) :
    ((sites.flatMap obs).filterMap Prod.snd).count g =
      (sites.map fun i => ((obs i).filterMap Prod.snd).count g).sum := by
  induction sites with
  | nil => rfl
  | cons i xs ih => simp [List.flatMap_cons,List.filterMap_append,ih]

/-- Every physical count operand for a passing merged private call contains the
total ID frequency of its original sites. The statement reads actual reported bits. -/
theorem merged_countOperand_pair (D : Directory) (bank : ℕ → Bool) (sites : List ι)
    (obs : ι → List (Bool × Option ℕ)) (read : D.observations bank = some (sites.flatMap obs))
    (pass : D.weight bank ≠ 0) (h zeroAddr refAddr : ℕ) (g : Fin D.reportedCounts.length) :
    (countOperand h zeroAddr refAddr D bank g).pair =
      (h+g.val,(sites.map fun i => ((obs i).filterMap Prod.snd).count g.val).sum) := by
  obtain ⟨seen,es,eq⟩ := countOperands_of_passing h zeroAddr refAddr D bank pass
  obtain rfl := Option.some.inj (es.symm.trans read)
  rw [eq,count_site_ids]

end CellSparse

end BorderVNP
end Computability
end OAI
