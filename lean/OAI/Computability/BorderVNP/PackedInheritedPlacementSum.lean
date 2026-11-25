import OAI.Computability.BorderVNP.PackedInheritedPlacementTies

/-! # Eliminating the final canonical incidence staging

For each assignment of the cell's internal wires, the sparse ties force one
incidence word vector at each site. Its earlier private work remains free.
The packed cell-wide staging sum therefore factors into the actual private
site sums, with all multiplicities and weights retained.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Placement

open Crossing CellAddresses CellSparse
open scoped Classical

private def extent (s : Site) (z : Fin s.size → Bool) (j : ℕ) : Bool :=
  if h : j < s.size then z ⟨j,h⟩ else false

private noncomputable def slabValue {R : Type*} [Zero R] (s : Site) (weight : List (Bool × Option ℕ) → R)
    (input : Fin s.incoming → Bool) (z : Fin s.size → Bool) : R :=
  if (fun j => z (Fin.natAdd s.work j)) = input then (s.observe (extent s z)).elim 0 weight else 0

private theorem sum_slab {R : Type*} [AddCommMonoid R] (s : Site) (weight : List (Bool × Option ℕ) → R)
    (input : Fin s.incoming → Bool) :
    (∑ z, slabValue s weight input z) = s.value weight input := by
  have split : (∑ z : Fin s.size → Bool, slabValue s weight input z) =
      ∑ gx : (Fin s.work → Bool) × (Fin s.incoming → Bool), slabValue s weight input (Fin.append gx.1 gx.2) :=
    ((Fin.appendEquiv (α := Bool) s.work s.incoming).sum_comp (slabValue s weight input)).symm
  rw [split,Fintype.sum_prod_type]
  unfold Site.value
  apply Finset.sum_congr rfl
  intro g _
  have h (x : Fin s.incoming → Bool) : slabValue s weight input (Fin.append g x) =
      if x = input then (s.observe (bits g x)).elim 0 weight else 0 := by
    unfold slabValue
    rw [show (fun j => Fin.append g x (Fin.natAdd s.work j)) = x from funext (Fin.append_right g x)]
    rfl
  change (∑ x, slabValue s weight input (Fin.append g x)) = _
  simp_rw [h]
  simp

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns)
    (edgeID : N.Edge ↪ Fin M) (portID : P ↪ Fin np) (state : N.Site → Site)
variable {R : Type*} [CommSemiring R] (weight : N.Site → List (Bool × Option ℕ) → R)
    (merged : List (List Factor)) (base : N.Site → ℕ) (g : Fin (guessedSize N cell c) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool)

private abbrev sizes := fun v => (state v).size
private noncomputable abbrev address (v : {v : N.Site // cell v = c}) := siteBase N cell c siteID (sizes N state) v

/-- Contribution of a physically located site program and all of its final binding rows on the cell bank. -/
noncomputable def siteFactor (v : {v : N.Site // cell v = c}) (a : Fin (siteSize N cell c (sizes N state)) → Bool) : R :=
  let bankBits := lookup (bank N cell c (sizes N state) g a x)
  if ∀ r ∈ ties N cell c siteID edgeID portID state v, r.Valid merged bankBits then
    ((state v.val).placedObserve merged (address N cell c siteID state v) (base v.val) bankBits).elim 0 (weight v.val)
  else 0

variable (hs : ∀ v, (state v).incoming = incoming N v) (loc : ∀ v, (state v).Local)
    (fit : ∀ v r, r ∈ (state v).rows → r.BoxRefFits (state v).boxes.length)
    (span : ∀ v : {v : N.Site // cell v = c}, base v.val + (state v.val).boxes.length ≤ merged.length)
    (get : ∀ v : {v : N.Site // cell v = c}, ∀ j < (state v.val).boxes.length,
      merged.getD (base v.val+j) [] = (state v.val).boxes.getD j [])
    (fixed : ∀ v : {v : N.Site // cell v = c}, ∀ o ∈ (state v.val).directory.occurrences,
      o.factor.shift (address N cell c siteID state v) = o.factor)

private noncomputable abbrev expected (v : {v : N.Site // cell v = c}) :=
  canonical N cell c edgeID portID v g x ∘ Fin.cast (hs v.val)

include loc fit span get fixed in
private theorem siteFactor_eq (v : {v : N.Site // cell v = c}) (a : Fin (siteSize N cell c (sizes N state)) → Bool) :
    siteFactor N cell c siteID edgeID portID state weight merged base g x v a =
    slabValue (state v.val) (weight v.val) (expected N cell c edgeID portID state g x hs v)
      (siteWords N cell c siteID (sizes N state) a v) := by
  let s := state v.val
  let z := siteWords N cell c siteID (sizes N state) a v
  let off := address N cell c siteID state v
  let bankBits := lookup (bank N cell c (sizes N state) g a x)
  have guards : (∀ r ∈ ties N cell c siteID edgeID portID state v, r.Valid merged bankBits) ↔
      (fun j => z (Fin.natAdd s.work j)) = expected N cell c edgeID portID state g x hs v := by
    refine (ties_valid N cell c siteID edgeID portID state v (hs v.val) g a x merged).trans ?_
    constructor
    · intro eq
      funext j
      exact congrFun eq (Fin.cast (hs v.val) j)
    · intro eq
      funext j
      exact congrFun eq (Fin.cast (hs v.val).symm j)
  have value_eq : s.placedObserve merged off (base v.val) bankBits = s.observe (extent s z) := by
    rw [s.placed_observe merged off (base v.val) (fit v.val) (span v) (get v) (fixed v) bankBits]
    apply loc v.val
    intro j hj
    rw [extent,dite_eq_left hj]
    exact site_at N cell c (sizes N state) siteID g a x v ⟨j,hj⟩
  unfold siteFactor slabValue
  exact if_congr guards (congrArg (Option.elim · 0 (weight v.val)) value_eq) rfl

set_option maxHeartbeats 900000 in
include loc fit span get fixed in
/-- Eliminating all final staging guesses yields exactly the tensor's local product
for this cell, with the shared internal wire assignment held fixed. -/
theorem sum_siteFactor (table : N.Tables R)
    (models : ∀ v, (state v).Models N edgeID portID v (hs v) (weight v) table) :
    (∑ a, ∏ v : {v : N.Site // cell v = c},
      siteFactor N cell c siteID edgeID portID state weight merged base g x v a) =
    CellAddresses.factor N cell c edgeID portID table g x := by
  let term := fun z : ∀ v : {v : N.Site // cell v = c}, Fin ((state v.val).size) → Bool =>
    ∏ v, slabValue (state v.val) (weight v.val) (expected N cell c edgeID portID state g x hs v) (z v)
  calc
    _ = ∑ a, term (siteWords N cell c siteID (sizes N state) a) := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.prod_congr rfl; intro v _
      exact siteFactor_eq N cell c siteID edgeID portID state weight merged base g x hs loc fit span get fixed v a
    _ = ∑ z, term z := (siteWords N cell c siteID (sizes N state)).sum_comp term
    _ = ∏ v : {v : N.Site // cell v = c}, ∑ z : Fin ((state v.val).size) → Bool,
        slabValue (state v.val) (weight v.val) (expected N cell c edgeID portID state g x hs v) z :=
      (Fintype.prod_sum (fun (v : {v : N.Site // cell v = c}) z =>
        slabValue (state v.val) (weight v.val) (expected N cell c edgeID portID state g x hs v) z)).symm
    _ = CellAddresses.factor N cell c edgeID portID table g x := by
      unfold CellAddresses.factor
      apply Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
      intro v _
      exact (sum_slab (state v.val) (weight v.val) (expected N cell c edgeID portID state g x hs v)).trans
        (models v.val (fun e j => (wire N cell c edgeID portID v e j).elim g x) (fun p j => x (port N cell c edgeID portID v p j)))

include loc fit span get fixed in
/-- The complete sum of the physically relocated programs and their sparse bindings is
the contracted cell tensor on its actual crossing words and attached exterior ports. -/
theorem sum_cell [Fintype C] [DecidableEq C]
    (position : C → {z : EuclideanSpace ℝ (Fin D) // ‖z‖ ≤ 1}) (table : N.Tables R)
    (models : ∀ v, (state v).Models N edgeID portID v (hs v) (weight v) table)
    (w : ∀ e : Boundary N cell c, Fin (N.width e.val.val) → Bool)
    (args : ∀ u : {u : P // cell (N.attach u) = c}, Fin (bits u.val) → Bool) :
    let values : ∀ u : Supplied N cell c, Fin (suppliedWidth N cell c u) → Bool := fun u =>
      match u with | .inl e => w e | .inr p => args p
    let x := (suppliedWords N cell c edgeID portID).symm values
    (∑ g, ∑ a, ∏ v : {v : N.Site // cell v = c},
      siteFactor N cell c siteID edgeID portID state weight merged base g x v a) =
    N.cellTables cell position table c w args := by
  intro values x
  refine (Finset.sum_congr rfl (fun g _ => ?_)).trans (sum_factor N cell c edgeID portID position table w args)
  refine Eq.trans ?_ (sum_siteFactor N cell c siteID edgeID portID state
    weight merged base g x hs loc fit span get fixed table models)
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)

end Packing.Inherited.Placement

end BorderVNP
end Computability
end OAI
