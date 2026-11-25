import OAI.Computability.BorderVNP.PrivatePlacementPass
import OAI.Computability.BorderVNP.TransmissionDataPlacement

/-! # Separation of supplied inputs and staged private metadata in each cell

The original description records follow the complete supplied region. Their order inside
a cell is the order of the public original-site indices. No metadata bit has to be
interpreted as a live algebraic input to obtain its physical address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.PrivateBank

open Function
open scoped Classical

variable {A : Type*} [Fintype A] {entries cells M : ℕ}

/-- Concatenated public numbering, with the bounded IDs of genuine supplied words
before every original private metadata row. -/
def numbered (id : A ↪ Fin M) : (A ⊕ Fin entries) ↪ ℕ where
  toFun := Sum.elim (fun a => (id a).val) (fun j => M+j.val)
  inj' := by
    rintro (a|i) (b|j) h
    · exact congrArg Sum.inl (id.injective (Fin.ext h))
    · change (id a).val = M+j.val at h; have := (id a).isLt; omega
    · change M+i.val = (id b).val at h; have := (id b).isLt; omega
    · exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel h))

omit [Fintype A] in
private theorem numbered_left (id : A ↪ Fin M) (a : A) :
    numbered (entries := entries) id (.inl a) = (id a).val := rfl

omit [Fintype A] in
private theorem numbered_right (id : A ↪ Fin M) (j : Fin entries) :
    numbered id (.inr j) = M+j.val := rfl

variable (supplyCell : A → Fin cells) (originalCell : Fin entries → Fin cells)
    (id : A ↪ Fin M) (width : A → ℕ) (desc : ℕ)

/-- Supplied bit displacements are identical after appending the metadata suffix. -/
theorem base_supplied (a : A) :
    DataSlabs.base (Sum.elim supplyCell originalCell) (numbered id) (Sum.elim width (fun _ => desc)) (.inl a) =
      DataSlabs.base supplyCell (id.trans Fin.valEmbedding) width a := by
  simp only [DataSlabs.base,CellSlabs.start,Fintype.sum_sum_type,numbered_left,numbered_right,
    Sum.elim_inl,Sum.elim_inr,Embedding.trans_apply,Fin.valEmbedding_apply]
  have no (j : Fin entries) : ¬M+j.val < (id a).val := by have := (id a).isLt; omega
  simp only [no,ite_false,Finset.sum_const_zero,Nat.add_zero]
  apply Finset.sum_congr rfl
  intro x _; by_cases h : supplyCell x = supplyCell a <;> split_ifs <;> simp_all

/-- The starting offset of a private metadata row is the complete supplied width
plus exactly the increments written by the native per-cell counter. -/
theorem base_private (old : ℕ → ℕ) (owners : ∀ i : Fin entries, old i.val = (originalCell i).val)
    (i : Fin entries) :
    DataSlabs.base (Sum.elim supplyCell originalCell) (numbered id) (Sum.elim width (fun _ => desc)) (.inr i) =
      DataSlabs.size supplyCell width (originalCell i) +
        RoutingISA.PrivatePlacement.prefixCounts old desc i.val (originalCell i).val := by
  simp only [DataSlabs.base,CellSlabs.start,Fintype.sum_sum_type,numbered_left,numbered_right,
    Sum.elim_inl,Sum.elim_inr, Nat.add_lt_add_iff_left,DataSlabs.size]
  have first (a : A) : (id a).val < M+i.val := by have := (id a).isLt; omega
  simp only [first,ite_true]
  apply congrArg (_ + ·)
  have owner (j : Fin entries) : originalCell j = originalCell i ↔ old j.val = (originalCell i).val :=
    (Fin.ext_iff).trans (by rw [owners])
  simp only [owner,RoutingISA.PrivatePlacement.prefixCounts]
  let f := fun j : ℕ => if j < i.val then (if old j = (originalCell i).val then desc else 0) else 0
  change (∑ j : Fin entries, f j.val) = _
  rw [Fin.sum_univ_eq_sum_range f]
  calc
    _ = ∑ j ∈ Finset.range i.val, f j := (Finset.sum_subset (Finset.range_mono i.isLt.le) (by
      intro j _ hj
      simp only [Finset.mem_range] at hj
      simp [f,hj])).symm
    _ = _ := Finset.sum_congr rfl fun j hj => by simp [f, Finset.mem_range.mp hj]

/-- The metadata table produced by the native prefix pass and the live supplied-slot
table together realize an injective compact placement in the combined physical cell bank. -/
def placement {d : Layout} (pp lp : ℕ → ℕ × ℕ)
    (oldCell : Fin d.entries → Fin cells) (old : ℕ → ℕ)
    (owners : ∀ j : Fin d.entries, old j.val = (oldCell j).val)
    (live : (Fin d.teams × Fin d.sites) ↪ A) (liveWidth : ∀ k, width (live k) = d.block)
    (privateRows : ∀ j : Fin d.entries, pp j.val = ((oldCell j).val,
      DataSlabs.size supplyCell width (oldCell j) +
        RoutingISA.PrivatePlacement.prefixCounts old d.description j.val (oldCell j).val))
    (liveRows : ∀ k : Fin d.teams × Fin d.sites, lp (k.1.val*d.sites+k.2.val) =
      ((supplyCell (live k)).val,DataSlabs.base supplyCell (id.trans Fin.valEmbedding) width (live k))) :
    BankPlacement d pp lp (A ⊕ Fin d.entries) (Sum.elim supplyCell oldCell) (numbered id)
      (Sum.elim width fun _ => d.description) where
  key := { toFun := Sum.elim Sum.inr (Sum.inl ∘ live)
           inj' := by
             rintro (a|b) (c|e) h
             · exact congrArg Sum.inl (Sum.inr.inj h)
             · cases h
             · cases h
             · exact congrArg Sum.inr (live.injective (Sum.inl.inj h)) }
  width_eq k := by cases k with | inl j => rfl | inr t => exact liveWidth t
  entry k := by
    cases k with
    | inl j => exact (privateRows j).trans (congrArg (Prod.mk (oldCell j).val)
        (base_private supplyCell oldCell id width d.description old owners j).symm)
    | inr t => exact (liveRows t).trans (congrArg (Prod.mk (supplyCell (live t)).val)
        (base_supplied supplyCell oldCell id width d.description (live t)).symm)

end Packing.Directory.PrivateBank

end BorderVNP
end Computability
end OAI
