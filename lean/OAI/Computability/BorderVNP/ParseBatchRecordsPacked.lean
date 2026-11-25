import OAI.Computability.BorderVNP.ParseBatchRecords
import Mathlib.Data.Nat.Log

/-! # Fixed-width fields for the guessed preorder records of Lemma 2.3 -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP

/-- Two tag bits and six unsigned words suffice for a parse record. The variable of a
terminal is a bit position paired with its selected Boolean value. -/
structure Fields where
  /-- True for a binary production, false for a terminal. -/
  binary : Bool
  /-- Grammar state of this node. -/
  parent : ℕ
  /-- Number of leaves in the subtree minus one. -/
  layer : ℕ
  /-- Number of leaves in the left subtree minus one, used only in a production. -/
  split : ℕ
  /-- State of the left child. -/
  left : ℕ
  /-- State of the right child. -/
  right : ℕ
  /-- Query position used only by a terminal. -/
  pos : ℕ
  /-- Requested bit at the query position. -/
  bit : Bool
  deriving DecidableEq

variable {m g n : ℕ}

/-- Canonical word fields for a table label, setting every unused field to zero. -/
def pack : GrammarLabel (Fin m × Bool) (Fin g) n → Fields
  | .inl (h, v, b) => ⟨false, h.val, 0, 0, 0, 0, v.val, b⟩
  | .inr ⟨d, h, k, i, j⟩ => ⟨true, h.val, d.val, k.val, i.val, j.val, 0, false⟩

/-- Decode a guessed record, rejecting out-of-range fields and nonzero padding. -/
def unpack (m g n : ℕ) (a : Fields) : Option (GrammarLabel (Fin m × Bool) (Fin g) n) :=
  if hh : a.parent < g then
    if a.binary then
      if h : a.layer < n ∧ a.split < a.layer ∧ a.left < g ∧ a.right < g ∧
          a.pos = 0 ∧ a.bit = false then
        some (.inr ⟨⟨a.layer, h.1⟩, ⟨a.parent, hh⟩, ⟨a.split, h.2.1⟩,
          ⟨a.left, h.2.2.1⟩, ⟨a.right, h.2.2.2.1⟩⟩)
      else none
    else
      if h : a.pos < m ∧ a.layer = 0 ∧ a.split = 0 ∧ a.left = 0 ∧ a.right = 0 then
        some (.inl (⟨a.parent, hh⟩, ⟨a.pos, h.1⟩, a.bit))
      else none
  else none

/-- Every table label survives its range and padding checks. -/
theorem unpack_pack (t : GrammarLabel (Fin m × Bool) (Fin g) n) :
    unpack m g n (pack t) = some t := by
  rcases t with ⟨h, v, b⟩ | ⟨d, h, k, i, j⟩ <;> simp [pack, unpack]

/-- Every accepted encoding is canonical, including fields that its record type does not use. -/
theorem pack_of_unpack {a : Fields} {t : GrammarLabel (Fin m × Bool) (Fin g) n}
    (ha : unpack m g n a = some t) : pack t = a := by
  cases a with
  | mk tag h d b i j v bit =>
    cases tag <;> simp only [unpack, Bool.false_eq_true, ↓reduceIte] at ha
    all_goals
      split at ha <;> try contradiction
      split at ha <;> try contradiction
      have he := Option.some.inj ha
      subst t
      simp_all [pack]

/-- The range-check accepts a record exactly when its words are those of the decoded label. -/
theorem unpack_eq_some_iff {a : Fields} {t : GrammarLabel (Fin m × Bool) (Fin g) n} :
    unpack m g n a = some t ↔ a = pack t :=
  ⟨fun h => (pack_of_unpack h).symm, fun h => h ▸ unpack_pack t⟩

/-- A common bit width for every numerical field of a preorder record. -/
def recordWidth (m g n : ℕ) : ℕ := Nat.clog 2 (max m (max g n) + 1)

/-- All six words of an accepted record fit in the advertised width. The two remaining
fields are single Boolean bits. -/
theorem fields_fit (t : GrammarLabel (Fin m × Bool) (Fin g) n) :
    let a := pack t
    let B := 2 ^ recordWidth m g n
    a.parent < B ∧ a.layer < B ∧ a.split < B ∧ a.left < B ∧ a.right < B ∧ a.pos < B := by
  have bound : max m (max g n) < 2 ^ recordWidth m g n :=
    Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _)
  rcases t with ⟨h, v, b⟩ | ⟨d, h, k, i, j⟩
  · simp only [pack]
    have := h.isLt; have := v.isLt; omega
  · simp only [pack]
    have := h.isLt; have := d.isLt; have := k.isLt; have := i.isLt; have := j.isLt
    omega

end ParseRecords

end BorderVNP
end Computability
end OAI
