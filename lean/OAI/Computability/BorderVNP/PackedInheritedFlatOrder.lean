import OAI.Computability.BorderVNP.PackedInheritedDenseOrder
import OAI.Computability.BorderVNP.ShortenAdaptiveFlatten

/-! # Private incidence order on a flattened pack's free ports

The final public port has a flat copy number and its original slot. Transport
the public port row through that bijection. Its numerical ID, width and local
address then coincide with those used by the last shortening epoch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Flat

open Crossing Shortening Adaptive CellAddresses
open private start_equiv from OAI.Computability.BorderVNP.PackedInheritedDenseOrder
open scoped Classical

variable {k D M np : ℕ} {P : Type} {bits : P → ℕ} {R : Type*} (b : ℕ)
    (p : Pack D (Port k P b) (width bits k b) R) (rows : p.layout.Edge ↪ Fin M)
    (portID : Port k P b ↪ Fin np) (v : p.layout.Site)

/-- The stable exterior port IDs expressed on flat leaf and port indices. -/
def portRows (ids : Port k P b ↪ Fin np) : Fin (k^b) × P ↪ Fin np :=
  (portEquiv k P b).symm.toEmbedding.trans ids

private abbrev L := (flattenPack b p).layout

/-- Exactly the original attached words with their flat free-port labels. -/
def attached : Attached p.layout v ≃ Attached (L b p) v :=
  (portEquiv k P b).subtypeEquiv (fun u => by
    change p.layout.attach u = v ↔ p.layout.attach ((portEquiv k P b).symm (portEquiv k P b u)) = v
    rw [Equiv.symm_apply_apply])

private def supplied : Supplied p.layout id v ≃ Supplied (L b p) id v :=
  Equiv.sumCongr (Equiv.refl _) (attached b p v)

private theorem supply_width (u : Supplied p.layout id v) :
    suppliedWidth (L b p) id v (supplied b p v u) = suppliedWidth p.layout id v u := by
  rcases u with e|x
  · rfl
  · exact (width_portEquiv bits k b x.val).symm

private theorem supply_row (u : Supplied p.layout id v) :
    suppliedRow (L b p) id v rows (portRows b portID) (supplied b p v u) =
    suppliedRow p.layout id v rows portID u := by
  rcases u with e|x
  · rfl
  · have he : portRows b portID (attached b p v x).val = portID x.val :=
      congrArg portID ((portEquiv k P b).symm_apply_apply x.val)
    exact congrArg (fun j => (finSumFinEquiv (Sum.inr j : Fin (M+M) ⊕ Fin np)).val) he

variable [Fintype P] [Fintype (Port k P b)]

/-- Flat port names give the same full local incidence capacity. -/
theorem incoming_eq : incoming (flattenPack b p).layout v = incoming p.layout v := by
  unfold incoming
  congr 1
  unfold suppliedSize
  rw [←(supplied b p v).sum_comp]
  exact Finset.sum_congr rfl (fun x _ => supply_width b p v x)

private theorem supply_start (u : Supplied p.layout id v) :
    CellSlabs.start (suppliedRow (L b p) id v rows (portRows b portID)) (suppliedWidth (L b p) id v) (supplied b p v u) =
    CellSlabs.start (suppliedRow p.layout id v rows portID) (suppliedWidth p.layout id v) u :=
  start_equiv (supplied b p v) _ _ _ _ (supply_row b p rows portID v) (supply_width b p v) u

/-- Cable starts keep their old local ordinals after port flattening. -/
theorem wireStart_eq (z : Incident p.layout v) :
    wireStart (flattenPack b p).layout rows (portRows b portID) v z = wireStart p.layout rows portID v z := by
  unfold wireStart wireBase
  by_cases h : p.layout.src z.val = p.layout.dst z.val
  · rw [dite_eq_left (show id ((L b p).src z.val) = id ((L b p).dst z.val) from h),
      dite_eq_left (show id (p.layout.src z.val) = id (p.layout.dst z.val) from h)]
    rfl
  · rw [dite_eq_right (show id ((L b p).src z.val) ≠ id ((L b p).dst z.val) from h),
      dite_eq_right (show id (p.layout.src z.val) ≠ id (p.layout.dst z.val) from h)]
    exact congrArg (_ + ·) (supply_start b p rows portID v (.inl ⟨⟨z.val,h⟩,z.property⟩))

/-- The start of a port word at its flat copy-and-port label. -/
theorem portStart_eq (u : Attached p.layout v) :
    portStart (flattenPack b p).layout rows (portRows b portID) v (attached b p v u) =
    portStart p.layout rows portID v u :=
  congrArg (_ + ·) (supply_start b p rows portID v (.inr u))

end Packing.Inherited.Flat

end BorderVNP
end Computability
end OAI
