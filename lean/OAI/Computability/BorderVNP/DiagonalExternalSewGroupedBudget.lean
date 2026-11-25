import OAI.Computability.BorderVNP.DiagonalExternalGridBlockHosts
import OAI.Computability.BorderVNP.DiagonalExternalSewCellBudget

/-! # Per-cell sewing costs on the actual group of repeated bottom grids -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.GridHosts

open Cover Crossing Shortening Packing Packing.DeckGrid TeamContraction
open scoped Classical BigOperators

variable {R r t pins link inner n D : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (q depth : ℕ) (order : Fin (tileCount q depth) ≃ (Fin q → Deck (depth+2)))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (groups copies : ℕ) (count : groups*copies = R+1)
    (L : Network D (Fin groups × Fin (tileCount q depth)) (fun _ => copies*inputBlockWidth r n q depth))
    (ret : Retains (groupedBottom G q depth order position groups copies) L)

/-- The repeated teams in one bottom bundle use the original grouped
port of that bundle and tile at the true compressed vertex. -/
theorem groupOwner_eq (a : FreeBlock R (tileCount q depth)) :
    (blockHosts G q depth order position groups copies count L ret).groupOwner a =
      L.attach ((teamBlocks groups copies count a.1).1,a.2) := by
  rw [ret.attach]
  change ret.site ⟨_,baseHost (S := Fin q → Deck (depth+2)) order a.2.val⟩ = ret.site ⟨_,order a.2⟩
  rw [baseHost_val]

variable (h : BlockHosts (R := R) (r := r) (w := G.program.length+t) (link := link)
    (FineView.layout L (groupedLane G (tileCount q depth) Fintype.card_pos groups copies count))
    (Equiv.refl (PublicPort R r (G.program.length+t) link)) (inputBlockWidth r n q depth))
    (owner : ∀ a : FreeBlock R (tileCount q depth),
      h.groupOwner a = L.attach ((teamBlocks groups copies count a.1).1,a.2))

include owner in
private theorem sum_owners (k : ℕ) (test : L.Site → Prop) :
    testedWidth (fun _ : FreeBlock R (tileCount q depth) => k)
      (fun a => test (h.groupOwner a)) =
      testedWidth (fun _ : Fin groups × Fin (tileCount q depth) => copies*k) (fun a => test (L.attach a)) := by
  let Y := Fin groups × Fin (tileCount q depth)
  let pair := (teamBlocks groups copies count).trans (Equiv.prodComm _ _)
  let eqv : FreeBlock R (tileCount q depth) ≃ Fin copies × Y :=
    (pair.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)
  let f := fun a : Y => if test (L.attach a) then k else 0
  unfold testedWidth
  calc
    _ = ∑ z : Fin copies × Y, f z.2 := by
      apply Fintype.sum_equiv eqv
      intro a
      change (if test (h.groupOwner a) then k else 0) = f (eqv a).2
      rw [owner a]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      change (∑ _ : Fin copies, ∑ a : Y, f a) = _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hp : test (L.attach a) <;> simp [f,hp]

include owner in
/-- On a chosen final cell, charge all exterior cable ends and all literal
and pin groups against the true grouped input ports retained in that cell.
No counted address represents a different original team. -/
theorem grouped_records_of_owner (hg : 0 < inputBlockWidth r n q depth) (small : inputBlockWidth r n q depth ≤ link)
    (expanded : Bool) (prior payload : L.Site → ℕ) (test : L.Site → Prop) :
    localRecords (h.bundle.freeGroups h.groupOwner : Network D (FreeBlock R (tileCount q depth))
      (fun _ => inputBlockWidth r n q depth)) expanded prior payload test ≤
      (if expanded then 7 else 5*copies) * localRecords L expanded prior payload test := by
  let g := inputBlockWidth r n q depth
  let room := gridRoom G (V := tileCount q depth) Fintype.card_pos
  have hbound := h.grouped_cell hg small room expanded prior payload test
  refine hbound.trans ?_
  rw [sum_owners G q depth groups copies count L h owner]
  let factor := if expanded then 7 else 5*copies
  have hc : 0 < copies := by
    by_contra! hx
    have : copies = 0 := by omega
    simp [this] at count
  have hf : 1 ≤ factor := by
    cases expanded <;> simp [factor]
    omega
  have hbox : boxCableRecords L expanded prior payload test ≤ factor * boxCableRecords L expanded prior payload test :=
    Nat.le_mul_of_pos_left _ hf
  change boxCableRecords L expanded prior payload test + _ ≤ factor *
    (boxCableRecords L expanded prior payload test +
      testedWidth (fun _ : Fin groups × Fin (tileCount q depth) => recordCost expanded (copies*g))
        (fun a => test (L.attach a)))
  rw [Nat.mul_add factor (boxCableRecords L expanded prior payload test) _]
  apply Nat.add_le_add hbox
  unfold testedWidth
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : test (L.attach a)
  · simp only [ite_eq_left ha]
    cases expanded
    · simp [factor,recordCost]
      omega
    · change copies * (5+2*g) ≤ 7*(1+copies*g)
      have hn : copies ≤ copies*g := Nat.le_mul_of_pos_right _ hg
      nlinarith
  · simp [ha]

/-- Specialization to the block hosts retained from the original repeated bottom grids. -/
theorem grouped_records (hg : 0 < inputBlockWidth r n q depth) (small : inputBlockWidth r n q depth ≤ link)
    (expanded : Bool) (prior payload : L.Site → ℕ) (test : L.Site → Prop) :
    let h := blockHosts G q depth order position groups copies count L ret
    localRecords (h.bundle.freeGroups h.groupOwner : Network D (FreeBlock R (tileCount q depth))
      (fun _ => inputBlockWidth r n q depth)) expanded prior payload test ≤
      (if expanded then 7 else 5*copies) * localRecords L expanded prior payload test :=
  grouped_records_of_owner G q depth groups copies count L _ (groupOwner_eq G q depth order position groups copies count L ret)
    hg small expanded prior payload test

/-- Closing the physical exterior links adds at most the total per-team
incidence budget to the intercell width of the actual compressed pack. -/
theorem grouped_intercell_increment_of_hosts {Cell : Type*} (cell : L.Site → Cell) (X₀ : ℕ)
    (exterior : r*R*link ≤ X₀) :
    intercellWidth (h.bundle.freeGroups h.groupOwner : Network D (FreeBlock R (tileCount q depth))
      (fun _ => inputBlockWidth r n q depth)) cell ≤ intercellWidth L cell + (R+1)*X₀ := by
  let w := G.program.length+t
  let g := inputBlockWidth r n q depth
  have full : 2*(∑ c : Cables R r w link g, cableWidth c) = (R+1)*(r*R*link) :=
    twice_physical_width (R := R) (r := r) w (2*w+R*link) link g
  have cap := Nat.mul_le_mul_left (R+1) exterior
  have sumBound : (∑ c : Cables R r w link g, cableWidth c) ≤ (R+1)*X₀ := by omega
  exact (h.bundle.intercell_le cell).trans (Nat.add_le_add_left sumBound _)

/-- Width increment for the block hosts retained from the original repeated bottom grids. -/
theorem grouped_intercell_increment {Cell : Type*} (cell : L.Site → Cell) (X₀ : ℕ)
    (exterior : r*R*link ≤ X₀) :
    let h := blockHosts G q depth order position groups copies count L ret
    intercellWidth (h.bundle.freeGroups h.groupOwner : Network D (FreeBlock R (tileCount q depth))
      (fun _ => inputBlockWidth r n q depth)) cell ≤ intercellWidth L cell + (R+1)*X₀ :=
  grouped_intercell_increment_of_hosts G q depth groups copies count L _ cell X₀ exterior

/-- The final compact free words use the same original cables and actual
sewn interval edges as the cube input. Every added crossing between cells
is paid for by the physical exterior incidence budget. -/
theorem grouped_intercell {Cell : Type*} (cell : L.Site → Cell) (X₀ : ℕ)
    (inside : intercellWidth L cell ≤ (R+1)*X₀) (exterior : r*R*link ≤ X₀) :
    let h := blockHosts G q depth order position groups copies count L ret
    intercellWidth (h.bundle.freeGroups h.groupOwner : Network D (FreeBlock R (tileCount q depth))
      (fun _ => inputBlockWidth r n q depth)) cell ≤ 2*(R+1)*X₀ := by
  let h := blockHosts G q depth order position groups copies count L ret
  exact Bundle.physical_intercell_le (G.program.length+t) (2*(G.program.length+t)+R*link) link
    (inputBlockWidth r n q depth) h.bundle cell X₀ inside exterior

end Diagonal.ExternalSew.GridHosts

end BorderVNP
end Computability
end OAI
