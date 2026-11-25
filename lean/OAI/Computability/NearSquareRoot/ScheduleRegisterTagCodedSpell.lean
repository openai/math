import OAI.Computability.NearSquareRoot.ScheduleRegisterTagCodedArithmetic
import OAI.Computability.NearSquareRoot.InterchangeROMTableSpelling

/-! # Literal spellings of the scale-pass registers

A nested column places a fork marker before each bit except its final bit.
The parity register and the saved column rank use unary rulers. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterTagCoded

open IntegerMultiplication.Code
open GeneratorSyntax (ltr)
open KernelSelectorAlign (Column get)
open KernelComputableAddress

private def fromDigits (a : ℕ) (d : ℕ → ℕ) : List ℕ :=
  (List.range a).flatMap (fun i => [2,d i]) ++ [d a]

private theorem fromDigits_succ (a : ℕ) (d : ℕ → ℕ) :
    fromDigits (a+1) d = 2 :: d 0 :: fromDigits a (fun i => d (i+1)) := by
  simp [fromDigits,List.range_succ_eq_map,List.flatMap_map]

private theorem fromDigits_spell (a : ℕ) (x : Column a) (d : ℕ → ℕ)
    (h : ∀ i : Fin (a+1), d i.val = (get a x i).toNat) :
    fromDigits a d = (send x).spell.map ltr := by
  induction a generalizing d with
  | zero =>
    change [d 0] = _
    rw [show d 0 = x.toNat from h 0]
    cases x <;> rfl
  | succ a ih =>
    obtain ⟨b,x⟩ := x
    rw [fromDigits_succ, show d 0 = b.toNat from h 0, ih x (fun i => d (i+1)) (fun i => h i.succ)]
    cases b <;> rfl

/-- Spelling of a nested column directly from its binary rank. -/
def columnWord (a k : ℕ) : List ℕ := fromDigits a (digit 2 k)

theorem columnWord_rank (a : ℕ) (x : Column a) :
    columnWord a (columnRank a x) = (send x).spell.map ltr :=
  fromDigits_spell a x _ (digit_columnRank a x)

/-- Spelling of a unary register, including its final empty-list marker. -/
def tallyWord (n : ℕ) : List ℕ := (send (tally n)).spell.map ltr

theorem tallyWord_eq (n : ℕ) : tallyWord n = (send (tally n)).spell.map ltr := rfl

theorem primrec_tallyWord : Primrec tallyWord := InterchangeROMTable.primrec_spelling_numeral

variable {X : Type*} [Primcodable X]

theorem primrec_columnWord {a k : X → ℕ} (ha : Primrec a) (hk : Primrec k) :
    Primrec fun x => columnWord (a x) (k x) := by
  apply Primrec.list_append.comp
  · apply Primrec.list_flatMap (Primrec.list_range.comp ha)
    exact (Primrec.list_cons.comp (Primrec.const 2) <| Primrec.list_cons.comp
      (primrec_digit (Primrec.const 2) (hk.comp Primrec.fst) Primrec.snd) (Primrec.const [])).to₂
  · exact Primrec.list_cons.comp (primrec_digit (Primrec.const 2) hk ha) (Primrec.const [])

end RegisterTagCoded

end NearSquareRoot
end Computability
end OAI
