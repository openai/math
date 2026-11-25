import OAI.Computability.BorderVNP.PackedSubdivisionGateOrder

/-! # Fixed public row order of the final incidence ties

Each original incidence contributes one tie, including empty words. A cable with both
ends at the same site contributes its canonical source-side row. Restricting the global
cable-and-port order to a site reproduces that site's intrinsic placement order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing Shortening.PublicCapacity Placement Subdivision
open private order_facts increasing from OAI.Computability.BorderVNP.PackedSubdivisionGateOrder
open scoped Classical

/-- Public index of a final tie: both endpoint slots of each cable precede all exterior ports. -/
def ordinal {m np : ℕ} : Gates.Old m np ≃ Fin (m*2+np) :=
  let side := (Equiv.prodCongr (Equiv.refl (Fin m)) finTwoEquiv.symm).trans finProdFinEquiv
  (side.sumCongr (Equiv.refl (Fin np))).trans finSumFinEquiv

/-- Complete static rectangle for final cable-end and exterior ties. -/
def staticRows (m np : ℕ) : List (Gates.Old m np) := (List.finRange (m*2+np)).map ordinal.symm

variable {D np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {s : Shape} (old : Rows s N) (portID : P ↪ Fin np)

/-- Filtering real enabled owners retains precisely their named incidences in their canonical
order. Zero-width cables and ports participate in the same ordering proof. -/
theorem selected_names (v : N.Site) (keep : Gates.Old s.edges np → Bool)
    (correct : ∀ t, keep t = true ↔ ∃ r : Placement.Row N v, Gates.nameOld old portID v r = t) :
    (staticRows s.edges np).filter keep = (ordered N old.edge portID v).map (Gates.nameOld old portID v) := by
  let xs := (List.finRange (s.edges*2+np)).filter fun i => keep (ordinal.symm i)
  let names := Gates.nameOld old portID v
  let f := ordinal ∘ names
  obtain ⟨dup,order,all⟩ := order_facts old portID v
  have inject : Function.Injective f := ordinal.injective.comp names.injective
  have mem (i) : i ∈ xs ↔ i ∈ (ordered N old.edge portID v).map f := by
    simp only [xs,List.mem_filter,List.mem_finRange,true_and,correct,List.mem_map,all,true_and]
    constructor
    · rintro ⟨r,hr⟩
      exact ⟨r,(congrArg ordinal hr).trans (ordinal.apply_symm_apply i)⟩
    · rintro ⟨r,hr⟩
      exact ⟨r,((ordinal.symm_apply_apply (names r)).symm.trans (congrArg ordinal.symm hr))⟩
  have perm := (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) (dup.map inject)).mpr mem
  have source : (List.finRange (s.edges*2+np)).Pairwise (· ≤ ·) :=
    List.ofFn_id _ ▸ (monotone_id : Monotone (id : Fin (s.edges*2+np) → _)).sortedLE_ofFn.pairwise
  have target : ((ordered N old.edge portID v).map f).Pairwise (· ≤ ·) :=
    List.Pairwise.map f (fun a b h => (increasing (extra := 0) old portID v a b h).le) order
  have same : xs = (ordered N old.edge portID v).map f := perm.eq_of_pairwise' (source.filter _) target
  rw [staticRows,List.filter_map]
  change xs.map ordinal.symm = _
  rw [same,List.map_map]
  simp only [f,names,Function.comp_def,Equiv.symm_apply_apply]

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI
