import OAI.Computability.BorderVNP.PackedInheritedPlacementSum
import OAI.Computability.BorderVNP.PackedBottomBoxValue

/-! # Signed observation products of merged physical directories

The scalar of a guarded one-copy factor is zero when its table read rejects.
Multiplication of these scalars in record order handles both unsuccessful
private reads and successful selections of a zero field entry. The combined
directory checks one public count for each actual field position. Its signed
weight times the executed power scanner is the product of the site scalars
exactly on the matching counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.MergeField

open CellSparse
open private mapM_product from OAI.Computability.BorderVNP.PackedBottomBoxValue
open scoped Classical

variable {K : Type*} [Field K] (values : ℕ → K)

/-- The field value of all successful private reads after the local record checks. -/
noncomputable def guarded (D : Directory) (bank : ℕ → Bool) : K :=
  if ∀ r ∈ D.records, r.Valid D.boxes bank then (D.observations bank).elim 0 (fieldWeight values) else 0

private theorem observations_eq (D : Directory) (bank : ℕ → Bool) :
    (D.observations bank).elim 0 (fieldWeight values) =
      (D.occurrences.map (fun o => (o.factor.observe bank o.offset o.copy).elim 0 (fieldEntry values))).prod := by
  have h := mapM_product D.occurrences (fun o => o.factor.observe bank o.offset o.copy) (fieldEntry values)
  exact (congrArg ((D.observations bank).elim 0) (funext (fieldWeight_eq_prod values))).trans h

private theorem guarded_product {A : Type*} (sites : List A) (ok : A → Prop) [DecidablePred ok] (f : A → K) :
    (if ∀ i ∈ sites, ok i then (sites.map f).prod else 0) =
    (sites.map (fun i => if ok i then f i else 0)).prod := by
  induction sites with
  | nil => simp
  | cons i sites ih =>
    by_cases hi : ok i
    · simp only [List.forall_mem_cons,hi,true_and,List.map_cons,List.prod_cons,ite_true,←ih]
      split <;> simp
    · simp [hi]

/-- Physical concatenation multiplies all local values in the actual stable order,
including rejection and zero-weight choices. Every local row sees the common box table. -/
theorem guarded_merge {A : Type*} (sites : List A) (boxes : A → List (List Factor))
    (rows : A → List Record) (reports : List (List ℕ)) (bank : ℕ → Bool) :
    guarded values (Directory.mergeSites sites boxes rows reports) bank =
    (sites.map (fun i => guarded values ⟨sites.flatMap boxes,rows i,[]⟩ bank)).prod := by
  let merged := sites.flatMap boxes
  let localDir := fun i => (⟨merged,rows i,[]⟩ : Directory)
  let ok := fun i => ∀ r ∈ rows i, r.Valid merged bank
  let f := fun i => ((localDir i).observations bank).elim 0 (fieldWeight values)
  have valid : (∀ r ∈ (Directory.mergeSites sites boxes rows reports).records,
      r.Valid (Directory.mergeSites sites boxes rows reports).boxes bank) ↔ ∀ i ∈ sites, ok i := by
    simp only [Directory.mergeSites,List.forall_mem_flatMap,ok,merged]
  have product : ((Directory.mergeSites sites boxes rows reports).observations bank).elim 0 (fieldWeight values) =
      (sites.map f).prod := by
    rw [observations_eq values,Directory.mergeSites_occurrences]
    let score := fun o : Occurrence => (o.factor.observe bank o.offset o.copy).elim 0 (fieldEntry values)
    have split (is : List A) :
        ((is.flatMap (fun i => (localDir i).occurrences)).map score).prod = (is.map f).prod := by
      induction is with
      | nil => rfl
      | cons i is ih =>
        simp only [List.flatMap_cons,List.map_append,List.prod_append,List.map_cons,List.prod_cons,ih]
        exact congrArg (· * _) (observations_eq values (localDir i) bank).symm
    exact split sites
  unfold guarded
  rw [if_congr valid product rfl]
  let _ : DecidablePred ok := fun i => List.decidableBAll (Record.Valid merged bank) (rows i)
  exact guarded_product sites ok f

/-- Report words match the actual aggregate read. A rejected table read needs no report choice. -/
def Matches (D : Directory) (bank : ℕ → Bool) : Prop :=
  ∀ obs, D.observations bank = some obs → countsValid bank D.reportedCounts obs

variable [Fintype K]

/-- Actual checker output times the finite-field power scanner on the reported bit lists. -/
noncomputable def checked (D : Directory) (bank : ℕ → Bool) (v : Fin D.reportedCounts.length → K) : K :=
  let counts := fun i : Fin D.reportedCounts.length => D.reportedCounts[i].map bank
  (D.weight bank : K) * FieldStack.productPaths (FieldPowers.program v) FieldPowers.factor (fun _ => 1)
    (1+∑ i, (2*(counts i).length+2)) (.visit (Fin.last _)) counts

/-- The exact count gate between the executed scanner and the unrestricted signed factor product. -/
theorem checked_eq (D : Directory) (bank : ℕ → Bool) (v : Fin D.reportedCounts.length → K) :
    checked D bank v = if Matches D bank then guarded (FieldPowers.entry v) D bank else 0 := by
  unfold checked
  rw [FieldPowers.cell_weight]
  unfold Matches guarded
  cases he : D.observations bank with
  | none => simp
  | some obs =>
    by_cases hg : ∀ r ∈ D.records, r.Valid D.boxes bank
    · by_cases hc : countsValid bank D.reportedCounts obs
      · simp [hc,fieldWeight]
      · simp [hc]
    · simp [hg]

/-- The common counts filter a product of individual site field factors. -/
theorem checked_merge {A : Type*} (sites : List A) (boxes : A → List (List Factor))
    (rows : A → List Record) (reports : List (List ℕ)) (bank : ℕ → Bool) (v : Fin reports.length → K) :
    let D := Directory.mergeSites sites boxes rows reports
    checked D bank v = if Matches D bank then
      (sites.map (fun i => guarded (FieldPowers.entry v) ⟨sites.flatMap boxes,rows i,[]⟩ bank)).prod else 0 := by
  dsimp only
  exact (checked_eq (Directory.mergeSites sites boxes rows reports) bank v).trans
    (if_congr Iff.rfl (guarded_merge (FieldPowers.entry v) sites boxes rows reports bank) rfl)

end Packing.Inherited.MergeField

end BorderVNP
end Computability
end OAI
