import OAI.Computability.BorderVNP.FiniteEvaluatorMergedSite
import OAI.Computability.BorderVNP.FiniteDiagonalOwnedCellProduct

/-! # Complete staged field packets and their original owned-cell sums -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Merged

open Crossing Packing Packing.CellAddresses Packing.Inherited CellSparse
open FiniteDiagonal FiniteDiagonal.FieldSiteDirectory
open Cube.Physical Cube.Physical.NativeAssignments Cube.Scatter.Assignment
open scoped BigOperators Classical
open private privateWires_append privateStaging_append from OAI.Computability.BorderVNP.CubePhysicalNativeAssignments

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000
set_option maxHeartbeats 800000

variable {D M np ns : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns)
  (edgeID : N.Edge ↪ Fin M) (portID : P ↪ Fin np) (state : N.Site → Site)
  (hs : ∀ v, (state v).incoming = incoming N v) (loc : ∀ v, (state v).Local)
  (schema : ∀ v, (state v).Schema) (relative : ∀ v, (state v).RelativeBoxes)
  {F : Type*} [Field F] (values : ℕ → F)

private theorem bits_lookup {a b : ℕ} (u : Fin a → Bool) (v : Fin b → Bool) :
    Inherited.bits u v = lookup (List.ofFn u ++ List.ofFn v) := by
  rw [← List.ofFn_fin_append]
  funext i
  by_cases hi : i < a+b
  · simp only [Inherited.bits,dite_eq_left hi]
    exact (by simpa only [List.append_nil] using lookup_prefix (Fin.append u v) [] ⟨i,hi⟩ :
      lookup (List.ofFn (Fin.append u v)) i = Fin.append u v ⟨i,hi⟩).symm
  · simp [Inherited.bits,hi,CellSparse.lookup]

private theorem observation_guarded (s : Site) (w : ℕ → Bool) :
    (s.observe w).elim 0 (fieldWeight values) = MergeField.guarded values s.directory w := by
  change (if ∀ r ∈ s.rows, r.Valid s.boxes w then s.directory.observations w else none).elim 0 (fieldWeight values) =
    (if ∀ r ∈ s.rows, r.Valid s.boxes w then (s.directory.observations w).elim 0 (fieldWeight values) else 0)
  by_cases pass : ∀ r ∈ s.rows, r.Valid s.boxes w
  · rw [ite_eq_left pass,ite_eq_left pass]
  · rw [ite_eq_right pass,ite_eq_right pass]
    rfl

include hs loc schema relative in
private theorem guarded_product (g : Fin (guessedSize N cell c) → Bool)
    (a : Fin (siteSize N cell c (fun v => (state v).size)) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) :
    let s := site N cell c siteID edgeID portID state
    (s.observe (Inherited.bits (Fin.append g a) x)).elim 0 (fieldWeight values) =
    ∏ v : {v : N.Site // cell v = c}, Placement.siteFactor N cell c siteID edgeID portID state
      (fun _ => fieldWeight values) (Placement.cellBoxes N cell c siteID state) (Placement.boxBase N cell c siteID state) g x v a := by
  intro s
  rw [observation_guarded,show s.directory = _ from directory_eq N cell c siteID edgeID portID state,bits_lookup,List.ofFn_fin_append,List.append_assoc]
  let sites := Placement.orderedSites N cell c siteID
  let merged := Placement.cellBoxes N cell c siteID state
  let base := Placement.boxBase N cell c siteID state
  let fac := fun v => Placement.siteFactor N cell c siteID edgeID portID state (fun _ => fieldWeight values) merged base g x v a
  unfold Placement.packet
  rw [MergeField.guarded_merge]
  have eq : (sites.map (fun v => MergeField.guarded values ⟨merged,
      Placement.siteRows N cell c siteID edgeID portID state base v,[]⟩
      (lookup (bank N cell c (fun u => (state u).size) g a x)))).prod = (sites.map fac).prod := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro v _
    simpa only [List.append_nil] using Placement.guarded_siteRows N cell c siteID edgeID portID state hs g a x values merged base loc
      (fun u r hr => (schema u r hr).1) (Placement.boxBase_fits N cell c siteID state) (Placement.boxBase_read N cell c siteID state)
      (fun u => (relative u.val).reachable _) v []
  have nodup : sites.Nodup := by apply Finset.sort_nodup
  have whole : sites.toFinset = Finset.univ := by apply Finset.sort_toFinset
  exact eq.trans ((List.prod_toFinset fac nodup).symm.trans (congrArg (Finset.prod · fac) whole))

include hs loc schema relative in
/-- The physical private vector includes all incoming copies and bindings.
Eliminating those forced staging lanes gives the product of the original
site tables, at the real incoming words and the guessed inside cables. -/
theorem value_factors (T : N.Tables F)
    (models : ∀ v, (state v).Models N edgeID portID v (hs v) (fieldWeight values) T)
    (x : Fin (suppliedSize N cell c) → Bool) :
    (site N cell c siteID edgeID portID state).value (fieldWeight values) x =
    ∑ g, CellAddresses.factor N cell c edgeID portID T g x := by
  let s := site N cell c siteID edgeID portID state
  let score := fun (b : Fin s.work → Bool) => (s.observe (Inherited.bits b x)).elim 0 (fieldWeight values)
  change (∑ b : Fin s.work → Bool, score b) = _
  refine ((Fin.appendEquiv (α := Bool) (guessedSize N cell c) (siteSize N cell c (fun v => (state v).size))).sum_comp score).symm.trans ?_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  refine (Finset.sum_congr rfl (fun a _ => guarded_product N cell c siteID edgeID portID state hs loc schema relative values g a x)).trans ?_
  exact Placement.sum_siteFactor N cell c siteID edgeID portID state (fun _ => fieldWeight values)
    (Placement.cellBoxes N cell c siteID state) (Placement.boxBase N cell c siteID state) g x hs loc
    (fun v r hr => (schema v r hr).1) (Placement.boxBase_fits N cell c siteID state) (Placement.boxBase_read N cell c siteID state)
    (fun v => (relative v.val).reachable _) T models

end FiniteEvaluator.Merged

end BorderVNP
end Computability
end OAI
