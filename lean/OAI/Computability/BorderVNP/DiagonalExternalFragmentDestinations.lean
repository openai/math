import OAI.Computability.BorderVNP.DiagonalExternalFragmentCables
import OAI.Computability.BorderVNP.CubeHostScatterReadback

/-! # Disjoint native host writes from the supplied slabs of the real network

Within a cell, each source or destination uses its own sparse supplied row.
Distinct cells use disjoint physical banks of the public stride.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses BorderVNP.Cube
open private ordinal_val from OAI.Computability.BorderVNP.DiagonalExternalFragmentCables

variable {D C m n : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    {N : Network D P bits} {cell : N.Site → Fin C} {edgeID : N.Edge ↪ Fin m} {portID : P ↪ Fin n}
    {l : HostScatter.Layout} {mem : ℕ → ℕ} (rows : CableRows N cell edgeID portID l mem)

include rows in
private theorem owned_geometry {i : ℕ} (hi : i < l.count) {side : Bool} (owned : l.Owned mem i side) :
    ∃ e : N.CrossingEdge cell, (edgeID e.val).val = i ∧ l.width mem i = N.width e.val ∧
      l.dest mem i side = mem (l.cells+2*(endpointCell N cell side e).val+1)+endpointRow N cell edgeID portID side e := by
  let q : Quad := ⟨l.cell mem i side,mem (l.relative+2*i+side.toNat),l.dest mem i side,l.width mem i⟩
  have found : cable l mem side i = some q := by simp [cable,owned.1,owned.2.1,q]
  obtain ⟨e,atID,_,eq⟩ := (cable_some_iff rows hi side q).mp found
  exact ⟨e,atID,congrArg Quad.width eq,congrArg Quad.source eq⟩

private theorem earlier_bank (origin stride : ℕ) (room : ∀ c : Fin C, suppliedSize N cell c ≤ stride)
    (s t : Bool) (e f : N.CrossingEdge cell) (lt : endpointCell N cell s e < endpointCell N cell t f) :
    origin+(endpointCell N cell s e).val*stride+endpointRow N cell edgeID portID s e+N.width e.val ≤
      origin+(endpointCell N cell t f).val*stride+endpointRow N cell edgeID portID t f := by
  have fit := (endpointRow_fits N cell edgeID portID s e).trans (room _)
  have cells := Nat.mul_le_mul_right stride (show (endpointCell N cell s e).val+1 ≤ (endpointCell N cell t f).val from lt)
  rw [Nat.add_mul,Nat.one_mul] at cells
  omega

private theorem distinct_rows {s t : Bool} {i k : ℕ} (hi : i < m) (hk : k < m)
    (ne : (i,s) ≠ (k,t)) : (if s then m else 0)+i ≠ (if t then m else 0)+k := by
  intro eq
  cases s <;> cases t <;> simp only [Bool.false_eq_true,ite_false,ite_true] at eq
  · exact ne (congrArg (fun z : ℕ => (z,false)) (by omega))
  · omega
  · omega
  · exact ne (congrArg (fun z : ℕ => (z,true)) (by omega))

include rows in
/-- Native writes at any two distinct owned endpoints are disjoint. Both
the within-cell order and the extent of each supplied word are derived
from the true sparse cable rows and the real final network. -/
theorem separate_destinations (origin stride : ℕ)
    (banks : ∀ c : Fin C, mem (l.cells+2*c.val+1) = origin+c.val*stride)
    (room : ∀ c : Fin C, suppliedSize N cell c ≤ stride) : l.SeparateDestinations mem := by
  intro i hi s hs k hk t ht ne
  obtain ⟨e,ei,wi,di⟩ := owned_geometry rows hi hs
  obtain ⟨f,fk,wk,dk⟩ := owned_geometry rows hk ht
  change _+_ ≤ _ ∨ _+_ ≤ _
  rw [wi,wk,di,dk,banks,banks]
  rcases lt_trichotomy (endpointCell N cell s e) (endpointCell N cell t f) with lower | same | upper
  · exact Or.inl (earlier_bank origin stride room s t e f lower)
  · have diff := distinct_rows (rows.count ▸ hi) (rows.count ▸ hk) ne
    rw [← ei,← fk] at diff
    rcases lt_or_gt_of_ne diff with lower | upper
    · have h := endpointRow_le N cell edgeID portID s t e f same lower
      rw [same]
      exact Or.inl (by omega)
    · have h := endpointRow_le N cell edgeID portID t s f e same.symm upper
      rw [same]
      exact Or.inr (by omega)
  · exact Or.inr (earlier_bank origin stride room t s f e upper)

include rows in
/-- The native chooser returns an increasing sparse embedding together with
its pointwise agreement with the physical edge IDs. The destination of every
positive crossing lane in that traversal is the canonical evaluator address. -/
theorem chosen_dest_lane {M K : ℕ} (ord : N.CrossingEdge cell ≃ Fin M) (row : Fin M ↪o Fin K)
    (loc : ∀ e, (row (ord e)).val = (edgeID e.val).val) (c : Fin C) (u : Boundary N cell c)
    (side : Bool) (here : endpointCell N cell side u.val = c) (j : Fin (N.width u.val.val)) :
    l.dest mem (row (ord u.val)).val side+j.val =
      mem (l.cells+2*c.val+1)+(suppliedOrdinal N cell c edgeID portID (.inl u) j).val := by
  let i := (edgeID u.val.val).val
  let q : Quad := ⟨l.cell mem i side,mem (l.relative+2*i+side.toNat),l.dest mem i side,l.width mem i⟩
  have hit := (rows.crossing side u.val).trans (ite_eq_left (Nat.zero_lt_of_lt j.isLt))
  have eq : q = actualQuad N cell edgeID portID l mem side u.val := by
    unfold cable at hit
    split at hit
    · contradiction
    · exact Option.some.inj hit
  have dest := congrArg Quad.source eq
  change l.dest mem i side = mem (l.cells+2*(endpointCell N cell side u.val).val+1)+endpointRow N cell edgeID portID side u.val at dest
  rw [loc]
  change l.dest mem i side+j.val = _
  rw [dest,here,Nat.add_assoc,endpointRow_at N cell edgeID portID c side u.val here]
  exact congrArg (_ + ·) (ordinal_val N cell edgeID portID c (.inl u) j).symm

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
