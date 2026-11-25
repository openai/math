import OAI.Computability.BorderVNP.FiniteLocalCell

/-! # The actual finite-field sparse entries of a local cell component -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteLocalCell

open Crossing FieldDirectory
open scoped BigOperators Classical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {Cell : Type} [Fintype Cell] [DecidableEq Cell] (cell : N.Site → Cell) (c : Cell)

omit [Fintype P] [Fintype Cell] [DecidableEq Cell] in
private theorem wire_injective (v : N.Site) : Function.Injective (FieldDirectory.wire N v) := by
  rintro (⟨⟨e,he⟩,i⟩ | ⟨⟨e,he⟩,i⟩) (⟨⟨e',he'⟩,j⟩ | ⟨⟨e',he'⟩,j⟩) h
  all_goals simp only [FieldDirectory.wire,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] at h
  all_goals cases h
  all_goals rfl

/-- The unique original wire or external port corresponding to a local bank bit. -/
def originalWire : Wire (network N cell c) → Wire N
  | .inl ⟨e,i⟩ => .inl ⟨e.val,i⟩
  | .inr ⟨.inl e,i⟩ => .inl ⟨e.val.val,i⟩
  | .inr ⟨.inr p,i⟩ => .inr ⟨p.val,i⟩

omit [Fintype P] [Fintype Cell] in
/-- A local private bit, crossing bit and external bit can never alias at this component. -/
theorem originalWire_injective : Function.Injective (originalWire N cell c) := by
  rintro (⟨⟨e,he⟩,i⟩ | ⟨(⟨⟨e,he⟩,hc⟩ | ⟨e,he⟩),i⟩)
    (⟨⟨e',he'⟩,j⟩ | ⟨(⟨⟨e',he'⟩,hc'⟩ | ⟨e',he'⟩),j⟩) h
  all_goals simp only [originalWire,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] at h
  all_goals cases h
  all_goals first | rfl | exact False.elim (he' (he.1.trans he.2.symm))
                  | exact False.elim (he (he'.1.trans he'.2.symm))

omit [Fintype P] [Fintype Cell] in
private theorem crossing_end (e : Boundary N cell c) :
    N.src e.val.val = (endpoint N cell c e).val ∨ N.dst e.val.val = (endpoint N cell c e).val := by
  unfold endpoint
  split <;> simp

/-- Each incident lane at a fine site in the cell comes from the exact
corresponding internal or external lane at that original site. -/
def originalLane (v : (network N cell c).Site) : Lane (network N cell c) v → Lane N v.val
  | .inl ⟨e,i⟩ => .inl ⟨⟨e.val.val, e.property.imp (congrArg Subtype.val) (congrArg Subtype.val)⟩,i⟩
  | .inr ⟨⟨.inl e,h⟩,i⟩ => .inl ⟨⟨e.val.val, (crossing_end N cell c e).imp
      (fun he => he.trans (congrArg Subtype.val h)) (fun he => he.trans (congrArg Subtype.val h))⟩,i⟩
  | .inr ⟨⟨.inr p,h⟩,i⟩ => .inr ⟨⟨p.val,congrArg Subtype.val h⟩,i⟩

omit [Fintype P] [Fintype Cell] in
private theorem originalLane_wire (v : (network N cell c).Site) (l : Lane (network N cell c) v) :
    wire N v.val (originalLane N cell c v l) = originalWire N cell c (wire (network N cell c) v l) := by
  rcases l with ⟨e,i⟩ | ⟨⟨e | p,h⟩,i⟩ <;> rfl

omit [Fintype P] [Fintype Cell] in
private theorem originalLane_inj (v : (network N cell c).Site) :
    Function.Injective (originalLane N cell c v) := by
  intro a b h
  apply wire_injective
  apply originalWire_injective N cell c
  simp only [← originalLane_wire, h]

omit [Fintype Cell] in
/-- Restricting to the local bank keeps every physical site at its original
degree bound, including loops and a boundary word that crosses a cell edge. -/
theorem lane_card_le (v : (network N cell c).Site) :
    Fintype.card (Lane (network N cell c) v) ≤ Fintype.card (Lane N v.val) := by
  exact Fintype.card_le_of_injective _ (originalLane_inj N cell c v)

variable {F : Type*} [Fintype F]

omit [Fintype Cell] in
/-- A literal trivalent site needs at most three locally numbered lane addresses
and eight scalar positions, even though many such sites share a public box. -/
theorem site_factor_size (table : N.Tables F) (v : (network N cell c).Site)
    (bound : Fintype.card (Lane N v.val) ≤ 3) :
    (addresses (network N cell c) v).length ≤ 3 ∧
    (rowIds (network N cell c) (tables N cell c table) v).length ≤ 8 := by
  apply literal_size (network N cell c) (tables N cell c table) v
  apply le_trans _ bound
  simp only [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective (originalLane N cell c v) (originalLane_inj N cell c v)

omit [Fintype Cell] in
/-- The sparse factor at one genuine site returns its fine-table field value
on the actual local hidden assignment and supplied public boundary. -/
theorem observe_site (table : N.Tables F) (v : (network N cell c).Site)
    (z : N.InsideAssignment cell c) (a x) (tail : ℕ → Bool) (copy : ℕ) :
    (factor (network N cell c) (tables N cell c table) v).observe
      (bank (network N cell c) z (ports N cell c a x) tail) 0 copy =
      some (false,some (Fintype.equivFin F (Diagonal.CellEntries.fineFactor cell table c z v a x)).val) := by
  rw [observe_factor]
  congr 4

end FiniteLocalCell

end BorderVNP
end Computability
end OAI
