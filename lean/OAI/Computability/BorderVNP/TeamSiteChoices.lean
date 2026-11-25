import OAI.Computability.BorderVNP.TeamPrivateValue
import OAI.Computability.BorderVNP.TeamPrivateCall

/-! # Choice prefixes for complete physical processor paths

The source RAM and the validator take binary choices at different clock ticks. An
infinite supply of bits lets both machines consume exactly their own finite prefix.
A bounded private machine determines that prefix on every supply, including the
branches whose contribution is zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteChoices

open TeamPrivateTape TeamPrivateFragment TeamPrivateValue

/-- An unlimited branch supply. Only a finite prefix contributes to a path. -/
abbrev Supply := ℕ → Bool

/-- First `n` choices, in consumption order. -/
def takeBits (s : Supply) (n : ℕ) := List.ofFn fun i : Fin n => s i.val

/-- Supply left to the continuation after a finite segment. -/
def drop (s : Supply) (n : ℕ) : Supply := fun i => s (n+i)

@[simp] theorem prefix_zero (s : Supply) : takeBits s 0 = [] := rfl

@[simp] theorem prefix_length (s : Supply) (n : ℕ) : (takeBits s n).length = n := List.length_ofFn

/-- Consume the first bit before running a continuation on the remaining stream. -/
theorem prefix_succ (s : Supply) (n : ℕ) : takeBits s (n+1) = s 0 :: takeBits (drop s 1) n := by
  rw [takeBits, List.ofFn_succ]
  congr 1
  simp only [takeBits, drop, Fin.val_succ, Nat.add_comm]

@[simp] theorem drop_zero (s : Supply) : drop s 0 = s := by funext i; simp [drop]

/-- Successive shifts of the choice stream add their offsets. -/
theorem drop_drop (s : Supply) (a b : ℕ) : drop (drop s a) b = drop s (a+b) := by
  funext i; simp only [drop, Nat.add_assoc]

/-- Consecutive portions of one stream concatenate in the order used by the processor. -/
theorem prefix_add (s : Supply) (a b : ℕ) : takeBits s (a+b) = takeBits s a ++ takeBits (drop s a) b := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, prefix_succ, prefix_succ, ih]
    simp only [List.cons_append, drop_drop, Nat.one_add]

variable {Q : Type} {d : ℕ}

/-- All bounded private tape paths, including rejecting halts, arise with their exact
finite choice prefix from an arbitrary supplied stream. -/
theorem private_prefix {P : Table Q d} {f q t} (halt : Stops P f q t) (s : Supply) :
    ∃ a n, a ≤ n ∧ n < f ∧ ∃ out u, Run P n q t (takeBits s a) out u := by
  induction f generalizing q t s with
  | zero => exact False.elim halt
  | succ f ih =>
    cases h : P q (heads t) with
    | halt accept neg =>
      exact ⟨0, 0, le_rfl, Nat.zero_lt_succ _, _, _, .stop h⟩
    | one c =>
      obtain ⟨a, n, ha, hn, out, u, run⟩ := ih (q := c.next) (t := c.apply t) (by simpa [Stops, h] using halt) s
      exact ⟨a, n+1, by omega, by omega, out, u, .one h run⟩
    | two l r =>
      let b := s 0
      let c := if b then r else l
      have both : Stops P f l.next (l.apply t) ∧ Stops P f r.next (r.apply t) := by simpa [Stops, h] using halt
      have hs : Stops P f c.next (c.apply t) := by cases hb : b <;> simp only [c, hb, Bool.false_eq_true, ↓reduceIte]; exacts [both.1, both.2]
      obtain ⟨a, n, ha, hn, out, u, run⟩ := ih hs (drop s 1)
      exact ⟨a+1, n+1, by omega, by omega, out, u, prefix_succ s a ▸ Run.two b h run⟩

/-- Extend any finite replay witness to a supply without changing its consumed bits. -/
def extend (bs : List Bool) : Supply := fun i => bs[i]?.getD false

/-- Reading the full original prefix from its extension returns exactly that witness. -/
theorem prefix_extend (bs : List Bool) : takeBits (extend bs) bs.length = bs := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [takeBits, extend]

end TeamSiteChoices

end BorderVNP
end Computability
end OAI
