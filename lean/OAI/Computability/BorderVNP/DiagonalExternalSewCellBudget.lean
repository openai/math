import OAI.Computability.BorderVNP.DiagonalExternalFreePhysical
import OAI.Computability.BorderVNP.DiagonalExternalSewGlobalRecords

/-! # Records charged at the true final cells after exterior sewing

Different teams in one bottom bundle retain the same physical site. The
bounds below sum by the original team and block, allowing all their
images to coincide in the final cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Finset
open scoped BigOperators Classical

variable {D R r w link g V : ℕ} {P : Type} {N : Network D P (fun _ => 1)}
    {physical : PublicPort R r w link ≃ P} (h : BlockHosts N physical g)
    (hg : 0 < g) (small : g ≤ link) (room : r*(2*w+R*link) ≤ V*g)

private def originKey (c : Bool × Cables R r w link g) : FreeBlock R V :=
  let a := fieldBlock w (2*w+R*link) link g c.2 c.1
  (a.1,⟨a.2,fieldBlock_lt _ _ _ _ V hg (by omega) room c.2 c.1⟩)

private theorem originKey_iff (c : Bool × Cables R r w link g) (a : FreeBlock R V) :
    originKey hg room c = a ↔ fieldBlock w (2*w+R*link) link g c.2 c.1 = (a.1,a.2.val) := by
  constructor
  · rintro rfl
    rfl
  · intro he
    have ht : (fieldBlock w (2*w+R*link) link g c.2 c.1).1 = a.1 := congrArg Prod.fst he
    have hs : (fieldBlock w (2*w+R*link) link g c.2 c.1).2 = a.2.val := congrArg Prod.snd he
    exact Prod.ext ht (Fin.ext hs)

include small in
private theorem perBlock (a : FreeBlock R V) (expanded : Bool) :
    (∑ c : {x : Bool × Cables R r w link g // originKey hg room x = a},
      recordCost expanded (cableWidth c.val.2)) ≤ 4 + if expanded then g else 0 := by
  let pred := fun c : Bool × Cables R r w link g =>
    fieldBlock w (2*w+R*link) link g c.2 c.1 = (a.1,a.2.val)
  let eqv := Equiv.subtypeEquivRight (fun c => originKey_iff hg room c a)
  have reorder :
      (∑ c : {x : Bool × Cables R r w link g // originKey hg room x = a},
        recordCost expanded (cableWidth c.val.2)) =
      ∑ c : {x // pred x}, recordCost expanded (cableWidth c.val.2) :=
    Fintype.sum_equiv eqv _ _ (fun _ => rfl)
  have hc : Fintype.card {x // pred x} ≤ 4 := by
    simpa only [Fintype.card_subtype] using
      physical_ends_per_block (r := r) w (2*w+R*link) link g (by omega) hg small a.1 a.2.val
  have hw := physical_width_per_block (r := r) w (2*w+R*link) link g (by omega) hg a.1 a.2.val
  rw [reorder]
  cases expanded
  · change (∑ _ : {x // pred x}, (1 : ℕ)) ≤ 4+0
    simpa using hc
  · change (∑ c : {x // pred x}, (1+cableWidth c.val.2)) ≤ 4+g
    rw [sum_add_distrib,sum_const,card_univ,nsmul_one,Nat.cast_id]
    exact Nat.add_le_add hc hw

include hg small room in
/-- At an arbitrary set of final host vertices, charge the exterior
incidences to the original team and block of each end. -/
theorem BlockHosts.endRecords_cell (expanded : Bool) (test : N.Site → Prop) :
    h.bundle.endRecords expanded test ≤
      testedWidth (fun _ : FreeBlock R V => 4 + if expanded then g else 0)
        (fun a => test (h.groupOwner a)) := by
  let A := Bool × Cables R r w link g
  let key := originKey (R := R) (r := r) (w := w) (link := link) hg room
  let val := fun c : A => if test (h.bundle.endpoint c.2 c.1) then recordCost expanded (cableWidth c.2) else 0
  have atKey (c : A) : h.bundle.endpoint c.2 c.1 = h.groupOwner (key c) := rfl
  change (∑ c : A, val c) ≤ ∑ a : FreeBlock R V, if test (h.groupOwner a) then _ else 0
  rw [← Fintype.sum_fiberwise key val]
  apply Finset.sum_le_sum
  intro a _
  have same (x : {x : A // key x = a}) : h.bundle.endpoint x.val.2 x.val.1 = h.groupOwner a :=
    (atKey x.val).trans (congrArg h.groupOwner x.property)
  by_cases ha : test (h.groupOwner a)
  · simp only [val,same,ite_eq_left ha]
    exact perBlock hg small room a expanded
  · simp only [val,same,ite_eq_right ha,sum_const_zero,le_refl]

include hg small room in
/-- The true compact network costs the unchanged boxes and internal cables,
plus at most five public records and two blocks of bits for each retained
team and original site in the cell. -/
theorem BlockHosts.grouped_cell (expanded : Bool) (prior payload : N.Site → ℕ) (test : N.Site → Prop) :
    localRecords (h.bundle.freeGroups h.groupOwner : Network D (FreeBlock R V) (fun _ => g))
        expanded prior payload test ≤
      boxCableRecords N expanded prior payload test +
        testedWidth (fun _ : FreeBlock R V => 5 + if expanded then 2*g else 0)
          (fun a => test (h.groupOwner a)) := by
  have before := h.bundle.localRecords_layout expanded prior payload test
  let free := testedWidth (fun _ : FreePort R r w => recordCost expanded 1)
    (fun f => test (N.attach (h.bundle.ports (.inl f))))
  change boxCableRecords h.bundle.layout expanded prior payload test + free =
    boxCableRecords N expanded prior payload test + free + h.bundle.endRecords expanded test at before
  have boxes : boxCableRecords h.bundle.layout expanded prior payload test =
      boxCableRecords N expanded prior payload test + h.bundle.endRecords expanded test := by omega
  change boxCableRecords h.bundle.layout expanded prior payload test +
    testedWidth (fun _ : FreeBlock R V => recordCost expanded g) (fun a => test (h.groupOwner a)) ≤ _
  rw [boxes, Nat.add_assoc]
  apply Nat.add_le_add_left
  refine (Nat.add_le_add_right (h.endRecords_cell hg small room expanded test) _).trans ?_
  unfold testedWidth
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : test (h.groupOwner a) <;> cases expanded <;> simp [ha,recordCost]
  omega

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
