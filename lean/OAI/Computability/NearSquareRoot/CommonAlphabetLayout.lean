import OAI.Computability.NearSquareRoot.CommonAlphabetCode
import OAI.Computability.IntegerMultiplication.TMModel
import Mathlib.Tactic

/-! # Block contents on a bi-infinite physical tape -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet
open IntegerMultiplication
variable {A : Type} (c : Code A)

/-- Cellwise encoding across the entire two-sided tape, independent of head location. -/
def SameCells (S : TM.Tape (Option Bool)) (T : TM.Tape A) : Prop :=
  ∀ (p : ℤ) (d : Fin c.width), S.absolute (p * c.width + d.val) = c.enc (T.absolute p) d

/-- At compiled instruction boundaries the head is at the first cell of the current block. -/
def Represents (S : TM.Tape (Option Bool)) (T : TM.Tape A) : Prop :=
  S.pos = T.pos * c.width ∧ SameCells c S T

theorem address_injective (p q : ℤ) (d e : Fin c.width) :
    p * c.width + d.val = q * c.width + e.val ↔ p = q ∧ d = e := by
  have div (p : ℤ) (d : Fin c.width) : (p * c.width + d.val) / c.width = p := by
    rw [add_comm, Int.add_mul_ediv_right _ _ (by exact_mod_cast c.pos.ne'),
      Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast d.isLt), zero_add]
  constructor
  · intro he
    have hp : p = q := by rw [← div p d, he, div]
    subst q
    exact ⟨rfl, Fin.ext (by exact_mod_cast add_left_cancel he)⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem tape_read {G : Type} (T : TM.Tape G) : T.absolute T.pos = T.view 0 := by
  simp [TM.Tape.absolute]

theorem idleWrite {G : Type} (S : TM.Tape G) (m : TM.Move) (p : ℤ) :
    (S.apply (S.view 0,m)).absolute p = S.absolute p := by
  rw [TM.Tape.absolute_apply]
  split
  · next he => rw [he, tape_read]
  · rfl

/-- After the first r writes the current virtual cell has a new prefix and its old suffix. -/
def Written (S : TM.Tape (Option Bool)) (T : TM.Tape A) (a : A) (r : ℕ) : Prop :=
  ∀ (p : ℤ) (d : Fin c.width), S.absolute (p * c.width + d.val) =
    if p = T.pos ∧ d.val < r then c.enc a d else c.enc (T.absolute p) d

theorem written_zero {S T} (h : SameCells c S T) (a : A) : Written c S T a 0 := by
  intro p d
  simpa using h p d

theorem written_succ {S T a} (j : Fin c.width) (h : Written c S T a j.val)
    (headAt : S.pos = T.pos * c.width + j.val) :
    Written c (S.apply (c.enc a j, .right)) T a (j.val+1) := by
  intro p d
  simp only [TM.Tape.absolute_apply, headAt, address_injective]
  rw [h p d]
  by_cases hp : p = T.pos
  · subst p
    by_cases he : d = j
    · subst d; simp
    · simp only [he, and_false, ite_false, true_and]
      split <;> split <;> simp_all [Fin.ext_iff] <;> omega
  · simp [hp]

theorem written_full {S T a} (h : Written c S T a c.width) (m : TM.Move) :
    SameCells c S (T.apply (a,m)) := by
  intro p d
  rw [h, TM.Tape.absolute_apply]
  by_cases e : p = T.pos <;> simp [e, d.isLt]

end CommonAlphabet

end NearSquareRoot
end Computability
end OAI
