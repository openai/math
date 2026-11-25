import OAI.Computability.BorderVNP.PackedInheritedMergeField
import OAI.Computability.BorderVNP.PackedInheritedPlacementWork

/-! # Merged site rows on the actual value stack with report operands

The cell's report words may follow the full guessed and supplied bank. All
staged incidence ties stay inside the preceding physical region. The site's
guarded observations read only its finite slab. Consequently appending these
operand bits preserves every local contribution before the count scan.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Placement

open CellSparse CellAddresses Crossing
open scoped Classical

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin M)
    (portID : P ↪ Fin np) (state : N.Site → Site)

private abbrev sizes := fun u => (state u).size
private noncomputable abbrev off (v : {v : N.Site // cell v = c}) := siteBase N cell c siteID (sizes N state) v
private noncomputable abbrev capacity := externalBase N cell c (sizes N state) + suppliedSize N cell c

/-- A live site's contribution to the final merged row list. -/
noncomputable def siteRows (base : N.Site → ℕ) (v : {v : N.Site // cell v = c}) : List Record :=
  (state v.val).placedRows (off N cell c siteID state v) (base v.val) ++ ties N cell c siteID edgeID portID state v

private theorem off_fits (v : {v : N.Site // cell v = c}) :
    off N cell c siteID state v+(state v.val).size ≤ capacity N cell c state :=
  (siteBase_fits N cell c siteID (sizes N state) v).trans (Nat.le_add_right _ _)

private theorem source_fits (v : {v : N.Site // cell v = c}) (r : Row N v.val) :
    physicalStart N cell c edgeID portID state v r + width N v.val r ≤ capacity N cell c state := by
  rcases r with e|p
  · change wireBase N cell c edgeID portID (sizes N state) v e + N.width e.val ≤ _
    unfold wireBase
    split
    · exact (CellSlabs.end_le_capacity _ _ _).trans
        ((Nat.le_add_right (guessedSize N cell c) (siteSize N cell c (sizes N state))).trans (Nat.le_add_right _ _))
    · rw [Nat.add_assoc]
      exact Nat.add_le_add_left (CellSlabs.end_le_capacity _ _ _) _
  · change portBase N cell c edgeID portID (sizes N state) v p + bits p.val ≤ _
    rw [portBase,Nat.add_assoc]
    exact Nat.add_le_add_left (CellSlabs.end_le_capacity _ _ _) _

private theorem local_fits (v : N.Site) (r : Row N v) :
    localStart N edgeID portID v r + width N v r ≤ incoming N v := by
  rcases r with e|p
  · exact wireEnd_le N edgeID portID v e
  · exact portEnd_le N edgeID portID v p

variable (hs : ∀ v, (state v).incoming = incoming N v)
    (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c (sizes N state)) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool)

private noncomputable abbrev region := bank N cell c (sizes N state) g a x

private theorem read_prefix (tail : List Bool) (j : ℕ) (hj : j < capacity N cell c state) :
    lookup (region N cell c state g a x ++ tail) j = lookup (region N cell c state g a x) j := by
  have h : j < (region N cell c state g a x).length := by
    simpa only [region,bank,List.length_append,List.length_ofFn,capacity,externalBase,Nat.add_assoc] using hj
  simp only [lookup,List.head?_drop,List.getElem?_append_left h]

include hs in
private theorem tie_read (v : {v : N.Site // cell v = c}) (r : Row N v.val) (boxes : List (List Factor)) (tail : List Bool) :
    (tie N cell c siteID edgeID portID state v r).Valid boxes (lookup (region N cell c state g a x ++ tail)) ↔
    (tie N cell c siteID edgeID portID state v r).Valid boxes (lookup (region N cell c state g a x)) := by
  change (∀ i < 1, ∀ j < _, _ = _) ↔ (∀ i < 1, ∀ j < _, _ = _)
  apply forall_congr'; intro i
  apply imp_congr_right; intro _
  apply forall_congr'; intro j
  apply imp_congr_right; intro hj
  have endS := off_fits N cell c siteID state v
  have hsize := hs v.val
  have endI := local_fits N edgeID portID v.val r
  have endP := source_fits N cell c edgeID portID state v r
  change off N cell c siteID state v+((state v.val).work+(state v.val).incoming) ≤ _ at endS
  have h₁ : off N cell c siteID state v+(state v.val).work+localStart N edgeID portID v.val r+j <
      capacity N cell c state := by omega
  have h₂ : physicalStart N cell c edgeID portID state v r+j < capacity N cell c state := by omega
  simp only [Port.atBit,Nat.mul_zero,Nat.add_zero,Nat.mul_one,
    read_prefix N cell c state g a x tail _ h₁,read_prefix N cell c state g a x tail _ h₂]

private theorem rows_observations (merged : List (List Factor)) (base : N.Site → ℕ)
    (v : {v : N.Site // cell v = c}) (bankBits : ℕ → Bool) :
    (⟨merged,siteRows N cell c siteID edgeID portID state base v,[]⟩ : Directory).observations bankBits =
    ((state v.val).placedDirectory merged (off N cell c siteID state v) (base v.val)).observations bankBits := by
  unfold Directory.observations
  congr 1
  have none (xs : List (Row N v.val)) : xs.flatMap (fun _ => ([] : List Occurrence)) = [] := by
    induction xs <;> simp_all
  simp only [Directory.occurrences,siteRows,List.flatMap_append,ties,List.flatMap_map,tie,none,List.append_nil,Site.placedDirectory]

variable {K : Type*} [Field K] (values : ℕ → K) (merged : List (List Factor)) (base : N.Site → ℕ)
    (loc : ∀ v, (state v).Local) (fit : ∀ v r, r ∈ (state v).rows → r.BoxRefFits (state v).boxes.length)
    (span : ∀ v : {v : N.Site // cell v = c}, base v.val + (state v.val).boxes.length ≤ merged.length)
    (get : ∀ v : {v : N.Site // cell v = c}, ∀ j < (state v.val).boxes.length,
      merged.getD (base v.val+j) [] = (state v.val).boxes.getD j [])
    (fixed : ∀ v : {v : N.Site // cell v = c}, ∀ o ∈ (state v.val).directory.occurrences,
      o.factor.shift (off N cell c siteID state v) = o.factor)

include hs loc fit span get fixed in
/-- The local row list of a merged cell on its stack with arbitrary trailing reports
evaluates to the same signed site contribution as the true physical bank. -/
theorem guarded_siteRows (v : {v : N.Site // cell v = c}) (tail : List Bool) :
    MergeField.guarded values ⟨merged,siteRows N cell c siteID edgeID portID state base v,[]⟩
        (lookup (region N cell c state g a x ++ tail)) =
    siteFactor N cell c siteID edgeID portID state (fun _ => fieldWeight values) merged base g x v a := by
  let s := state v.val
  let off := off N cell c siteID state v
  let pre := region N cell c state g a x
  let after := lookup (pre++tail)
  let before := lookup pre
  let bindings := ties N cell c siteID edgeID portID state v
  have ht : (∀ r ∈ bindings, r.Valid merged after) ↔ ∀ r ∈ bindings, r.Valid merged before := by
    simp only [bindings,ties,List.forall_mem_map]
    apply forall_congr'; intro r
    exact imp_congr_right fun _ => tie_read N cell c siteID edgeID portID state hs g a x v r merged tail
  have ho : s.placedObserve merged off (base v.val) after = s.placedObserve merged off (base v.val) before := by
    rw [s.placed_observe merged off (base v.val) (fit _) (span v) (get v) (fixed v) after,
        s.placed_observe merged off (base v.val) (fit _) (span v) (get v) (fixed v) before]
    apply loc v.val
    intro j hj
    exact read_prefix N cell c state g a x tail _ ((Nat.add_lt_add_left hj off).trans_le (off_fits N cell c siteID state v))
  have hrows : (∀ r ∈ siteRows N cell c siteID edgeID portID state base v, r.Valid merged after) ↔
      (∀ r ∈ s.placedRows off (base v.val), r.Valid merged after) ∧ ∀ r ∈ bindings, r.Valid merged after :=
    List.forall_mem_append
  unfold MergeField.guarded
  rw [rows_observations N cell c siteID edgeID portID state merged base v after]
  by_cases hb : ∀ r ∈ bindings, r.Valid merged before
  · have hb' := ht.mpr hb
    have he : (∀ r ∈ siteRows N cell c siteID edgeID portID state base v, r.Valid merged after) ↔
        ∀ r ∈ s.placedRows off (base v.val), r.Valid merged after := hrows.trans (and_iff_left hb')
    unfold siteFactor
    rw [ite_eq_left hb,←ho]
    unfold Site.placedObserve
    dsimp only [Site.placedDirectory]
    by_cases hr : ∀ r ∈ s.placedRows off (base v.val), r.Valid merged after
    · rw [ite_eq_left (he.mpr hr),ite_eq_left hr]
    · rw [ite_eq_right (mt he.mp hr),ite_eq_right hr]; rfl
  · have hn := mt ht.mp hb
    unfold siteFactor
    rw [ite_eq_right hb,ite_eq_right (fun h => hn (hrows.mp h).2)]

end Packing.Inherited.Placement

end BorderVNP
end Computability
end OAI
