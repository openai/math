import OAI.ThreeFlat.Diagonal.LaneCursorLayout

namespace OAI
/-! # Incidence counts in an XOR row layout -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout

open scoped Classical

variable {F : Type*} {p k low offsets slots : ℕ} {N : BitNetwork F p}
variable (P : RowLayout N k low offsets slots)

/-- The encoding of local slots bounds the number of owned cells. -/
theorem cells_at_most (v : Row k low) :
    Fintype.card {i : Fin N.cells // (P.cellAddress i).1 = v} ≤ slots := by
  classical
  let address := fun i : {i : Fin N.cells // (P.cellAddress i).1 = v} => (P.cellAddress i.val).2
  have injective : Function.Injective address := by
    intro i j h
    exact Subtype.ext (P.cellAddress.injective (Prod.ext (i.property.trans j.property.symm) h))
  simpa using Fintype.card_le_of_injective address injective

/-- A source row has at most three outgoing bit occurrences per offset and
slot. The bound counts every fanout branch separately. -/
theorem outgoing_at_most (v : Row k low) :
    Fintype.card {e : Occurrence N // P.owner e = v} ≤ offsets*(slots*3) := by
  classical
  let addr := fun a : {e : Occurrence N // P.owner e = v} =>
    (P.code a.val,(P.cellAddress a.val.val.1).2,a.val.val.2)
  have injective : Function.Injective addr := by
    intro a b h
    have ho := a.property.trans b.property.symm
    have hc : P.code a.val = P.code b.val := congrArg Prod.fst h
    have ha : (P.cellAddress a.val.val.1).2 = (P.cellAddress b.val.val.1).2 :=
      congrArg (fun z => z.2.1) h
    have hl : a.val.val.2 = b.val.val.2 := congrArg (fun z => z.2.2) h
    have hr : (P.cellAddress a.val.val.1).1 = (P.cellAddress b.val.val.1).1 := by
      have h₁ : (P.cellAddress a.val.val.1).1 = partner (P.owner a.val) (P.offset (P.code a.val)) := P.reaches _
      have h₂ : (P.cellAddress b.val.val.1).1 = partner (P.owner b.val) (P.offset (P.code b.val)) := P.reaches _
      rw [h₁,h₂,ho,hc]
    exact Subtype.ext (Subtype.ext (Prod.ext (P.cellAddress.injective (Prod.ext hr ha)) hl))
  simpa using Fintype.card_le_of_injective addr injective

end ThreeFlat.Diagonal.LaneCursor.RowLayout

end OAI
