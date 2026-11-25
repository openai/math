import OAI.Computability.BorderVNP.PackedInheritedPlacementSum

/-! # The canonical complete staging tape for an arbitrary original work tape

Each original site keeps every private choice. Its additional incoming slots
have one legal filling, computed from the independently supplied cable ends
and external ports. The sparse final ties recognize exactly these complete
tapes. This gives a pointwise correspondence before contraction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Placement

open Crossing CellAddresses CellSparse
open private slabValue extent siteFactor_eq from OAI.Computability.BorderVNP.PackedInheritedPlacementSum
open scoped Classical

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns)
    (edgeID : N.Edge ↪ Fin M) (portID : P ↪ Fin np) (state : N.Site → Site)
    (hs : ∀ v, (state v).incoming = incoming N v)

/-- Actual original work choices of all fine sites assigned to one cell. -/
abbrev Work := ∀ v : {v : N.Site // cell v = c}, Fin (state v.val).work → Bool

variable (g : Fin (guessedSize N cell c) → Bool) (x : Fin (suppliedSize N cell c) → Bool)

private abbrev sizes := fun v => (state v).size

/-- Insert the complete actual incident words into the physical staging tape. -/
noncomputable def install (w : Work N cell c state) : Fin (siteSize N cell c (sizes N state)) → Bool :=
  (siteWords N cell c siteID (sizes N state)).symm fun v =>
    Fin.append (w v) (canonical N cell c edgeID portID v g x ∘ Fin.cast (hs v.val))

/-- The intrinsic work portion of each complete slab. -/
noncomputable def extract (a : Fin (siteSize N cell c (sizes N state)) → Bool) : Work N cell c state :=
  fun v j => siteWords N cell c siteID (sizes N state) a v (Fin.castAdd (state v.val).incoming j)

/-- The site at its real staging interval reads its old work followed by the actual incoming words. -/
theorem read_install (w : Work N cell c state) (v : {v : N.Site // cell v = c}) :
    siteWords N cell c siteID (sizes N state) (install N cell c siteID edgeID portID state hs g x w) v =
    Fin.append (w v) (canonical N cell c edgeID portID v g x ∘ Fin.cast (hs v.val)) :=
  congrFun ((siteWords N cell c siteID (sizes N state)).apply_symm_apply _) v

/-- No old private choice is lost when the forced incidence bits are inserted. -/
theorem extract_install (w : Work N cell c state) :
    extract N cell c siteID state (install N cell c siteID edgeID portID state hs g x w) = w := by
  funext v j
  unfold extract
  rw [read_install,Fin.append_left]

/-- The final equality records recognize exactly the image of the installation map. -/
theorem install_iff (boxes : List (List Factor)) (a : Fin (siteSize N cell c (sizes N state)) → Bool) :
    (∀ v : {v : N.Site // cell v = c}, ∀ r ∈ ties N cell c siteID edgeID portID state v,
      r.Valid boxes (lookup (bank N cell c (sizes N state) g a x))) ↔
    install N cell c siteID edgeID portID state hs g x (extract N cell c siteID state a) = a := by
  constructor
  · intro checks
    apply (siteWords N cell c siteID (sizes N state)).injective
    funext v
    rw [read_install]
    apply funext
    refine Fin.addCases (fun j => ?_) (fun j => ?_)
    · exact Fin.append_left _ _ j
    · rw [Fin.append_right]
      have h := (ties_valid N cell c siteID edgeID portID state v (hs v.val) g a x boxes).mp (checks v)
      exact (congrFun h (Fin.cast (hs v.val) j)).symm
  · intro eq v
    apply (ties_valid N cell c siteID edgeID portID state v (hs v.val) g a x boxes).mpr
    funext j
    unfold staged
    rw [←eq,read_install,Fin.append_right]
    rfl

variable {R : Type*} [CommSemiring R] (weight : N.Site → List (Bool × Option ℕ) → R)
    (merged : List (List Factor)) (base : N.Site → ℕ)
    (loc : ∀ v, (state v).Local) (fit : ∀ v r, r ∈ (state v).rows → r.BoxRefFits (state v).boxes.length)
    (span : ∀ v : {v : N.Site // cell v = c}, base v.val + (state v.val).boxes.length ≤ merged.length)
    (get : ∀ v : {v : N.Site // cell v = c}, ∀ j < (state v.val).boxes.length,
      merged.getD (base v.val+j) [] = (state v.val).boxes.getD j [])
    (fixed : ∀ v : {v : N.Site // cell v = c}, ∀ o ∈ (state v.val).directory.occurrences,
      o.factor.shift (siteBase N cell c siteID (sizes N state) v) = o.factor)

include loc fit span get fixed in
/-- On each installed tape, the physically placed program has the field contribution of
this exact earlier work tape, with neither its sign nor its selected entries discarded. -/
theorem siteFactor_install (w : Work N cell c state) (v : {v : N.Site // cell v = c}) :
    siteFactor N cell c siteID edgeID portID state weight merged base g x v
      (install N cell c siteID edgeID portID state hs g x w) =
    ((state v.val).observe (Inherited.bits (w v) (canonical N cell c edgeID portID v g x ∘ Fin.cast (hs v.val)))).elim 0 (weight v.val) := by
  rw [siteFactor_eq N cell c siteID edgeID portID state weight merged base g x hs loc fit span get fixed,read_install]
  unfold slabValue
  rw [show (fun j => Fin.append (w v) (canonical N cell c edgeID portID v g x ∘ Fin.cast (hs v.val))
    (Fin.natAdd (state v.val).work j)) = canonical N cell c edgeID portID v g x ∘ Fin.cast (hs v.val) from
    funext (Fin.append_right _ _)]
  rw [ite_eq_left rfl]
  rfl

end Packing.Inherited.Placement

end BorderVNP
end Computability
end OAI
