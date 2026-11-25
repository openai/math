import OAI.Computability.BorderVNP.PackedInheritedRowNames

/-! # Stable filtering of the inherited-layer rectangle at a real site

The static source rectangle enumerates all candidate edge-side and port slots.
Selecting exactly the names incident at a site yields the precise chronological
order used in its installed program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Layer

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open scoped Classical

variable {D m old np : ℕ} {K : Type*} {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
variable (edgeID : p.layout.Edge ↪ Fin old) (portID : P ↪ Fin np) (v : p.layout.Site)

/-- Reading all live names in ascending rectangular ordinal produces exactly the
ordered local row list, including all zero-width real bands. -/
theorem filtered_names (keep : Row old D np → Bool)
    (real : ∀ r, keep r = true ↔ ∃ a, name p edgeID portID v a = r) :
    ((List.finRange (Fintype.card (Row old D np))).filter (fun i => keep (order.symm i))).map order.symm =
      List.ofFn (fun i => name p edgeID portID v (index p edgeID portID v i)) := by
  let M := Fintype.card (Row old D np)
  let n := Fintype.card (LayerRow p v)
  let ids := fun i : Fin n => order (name p edgeID portID v (index p edgeID portID v i))
  let left := (List.finRange M).filter fun i => keep (order.symm i)
  have mono : StrictMono ids := fun i j h => (index_lt p edgeID portID v i j).2 h
  have mem (i : Fin M) : i ∈ left ↔ i ∈ List.ofFn ids := by
    simp only [left,List.mem_filter,List.mem_finRange,true_and,real,List.mem_ofFn]
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨(index p edgeID portID v).symm a,by
        simp only [ids,Equiv.apply_symm_apply,ha]⟩
    · rintro ⟨a,ha⟩
      exact ⟨index p edgeID portID v a,by rw [←ha]; simp [ids]⟩
  have dup : (List.ofFn ids).Nodup := List.nodup_ofFn.mpr mono.injective
  have perm := (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) dup).mpr mem
  have sortedFin : (List.finRange M).Pairwise (· ≤ ·) :=
    List.ofFn_id M ▸ (monotone_id : Monotone (id : Fin M → Fin M)).sortedLE_ofFn.pairwise
  have eqn : left = List.ofFn ids := perm.eq_of_pairwise' (sortedFin.filter _) mono.monotone.sortedLE_ofFn.pairwise
  change left.map order.symm = _
  rw [eqn,List.map_ofFn]
  simp only [ids,Function.comp_def,Equiv.symm_apply_apply]
  rfl

variable [NeZero D] [Field K] (e : PaidIdentity K D m) {A : Type} [Fintype A]
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (binName : A → ℕ)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
variable {next : ℕ} (nextID : (output e p bin perm positive first q).layout.Edge ↪ Fin next)

/-- If each surviving physical row decodes its own slice, the dense section reads
exactly the entire layer of the site's private retained program. -/
theorem filtered_cuts (keep : Row old D np → Bool)
    (real : ∀ r, keep r = true ↔ ∃ a, name p edgeID portID v a = r) (read : Row old D np → Slice)
    (correct : ∀ a, read (name p edgeID portID v a) = layerSlice e p bin perm binName positive first q v edgeID nextID portID a) :
    (((List.finRange (Fintype.card (Row old D np))).filter (fun i => keep (order.symm i))).map order.symm).map read =
      orderedCuts p edgeID portID v e bin perm binName positive first q nextID := by
  rw [filtered_names p edgeID portID v keep real,List.map_ofFn]
  simp only [Function.comp_def,correct,orderedCuts]

end Packing.Inherited.Layer

end BorderVNP
end Computability
end OAI
