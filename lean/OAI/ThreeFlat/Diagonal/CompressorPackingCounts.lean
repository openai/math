import OAI.Computability.VPVNP.BitSlotIndex
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace OAI
/-! # Counting the two independent endpoint colors in the shrinking step -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression

variable {c d : ℕ} {V H Tag L : Type*}

/-- The other bits of a word are free once its values are prescribed at two
distinct colors. -/
def freeBits (i j : Fin c) (hne : i ≠ j) (a b : ZMod 2) :
    {w : BitWord c // w i = a ∧ w j = b} ≃
      ({t : Fin c // ¬(t = i ∨ t = j)} → ZMod 2) where
  toFun w t := w.val t.val
  invFun f := ⟨fun t =>
    if hi : t = i then a else if hj : t = j then b else f ⟨t, by aesop⟩,
    by simp [hne.symm]⟩
  left_inv w := by
    apply Subtype.ext
    funext t
    by_cases hi : t = i
    · subst t
      simpa using w.property.1.symm
    · by_cases hj : t = j
      · subst t
        simpa [hi] using w.property.2.symm
      · simp [hi, hj]
  right_inv f := by
    funext t
    have hi : t.val ≠ i := fun h => t.property (Or.inl h)
    have hj : t.val ≠ j := fun h => t.property (Or.inr h)
    simp [hi, hj]

theorem fixed_bit_count (i j : Fin c) (hne : i ≠ j) (a b : ZMod 2) :
    Fintype.card {w : BitWord c // w i = a ∧ w j = b} = 2 ^ (c - 2) := by
  rw [Fintype.card_congr (freeBits i j hne a b), Fintype.card_fun, ZMod.card,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq_or_eq_of_ne hne]

variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- The old wires of a single packed base arc, specified by the values of
the two endpoint tests. The source site fixes the tag and the remaining lane. -/
def endpointFiber (p : Site V Tag L × Fin d) (a b : ZMod 2) :=
  {q : BitWord c × H //
    q.1 (P.color p.1.1) = a ∧
      (q.1 + P.bitShift (p.1.1,p.2)) (P.color (P.slots.target (p.1.1,p.2)).1) = b}

/-- The destination color's required value is translated back to the
source. The old slot-label coordinate is unrestricted. -/
def endpointEquiv (p : Site V Tag L × Fin d) (a b : ZMod 2) :
    endpointFiber P p a b ≃
      {w : BitWord c // w (P.color p.1.1) = a ∧
        w (P.color (P.slots.target (p.1.1,p.2)).1) =
          b - P.bitShift (p.1.1,p.2) (P.color (P.slots.target (p.1.1,p.2)).1)} × H where
  toFun q := (⟨q.val.1, q.property.1, eq_sub_of_add_eq q.property.2⟩, q.val.2)
  invFun q := ⟨(q.1.val, q.2), q.1.property.1, eq_sub_iff_add_eq.mp q.1.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance endpointFintype [Fintype H] (p : Site V Tag L × Fin d) (a b : ZMod 2) :
    Fintype (endpointFiber P p a b) := Fintype.ofEquiv _ (endpointEquiv P p a b).symm

omit [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] in
/-- Every pair of endpoint bit values, including the thick--thick pair,
has exactly one quarter of the fibers over the packed base arc. -/
theorem endpoint_count [Fintype H] (p : Site V Tag L × Fin d) (a b : ZMod 2) :
    Fintype.card (endpointFiber P p a b) = 2 ^ (c - 2) * d := by
  rw [Fintype.card_congr (endpointEquiv P p a b), Fintype.card_prod,
    fixed_bit_count _ _ (P.proper (p.1.1,p.2)) _ _, Fintype.card_congr P.slotLabel, Fintype.card_fin]

/-- Translate the fiber description to the two actual `thick` tests. -/
theorem both_thick (p : Site V Tag L × Fin d) (w : BitWord c) (h : H) :
    (P.thick (sourcePosition (p,w,h)) ∧ P.thick (sourcePosition (P.actual (p,w,h)))) ↔
      w (P.color p.1.1) = 1 ∧
      (w + P.bitShift (p.1.1,p.2)) (P.color (P.slots.target (p.1.1,p.2)).1) = 1 := Iff.rfl

end ThreeFlat.Diagonal.CompressorPacking

end OAI
