import OAI.Computability.NearSquareRoot.ScheduleGeneratorAlphabetRows
import OAI.Computability.NearSquareRoot.ScheduleGeneratorReadStart

/-! # Computable ROM emission for a one-hot-serialized machine family -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Phase
open CommonAlphabet IntegerMultiplication
variable {A Q : ℕ → Type} {I : Type}
variable (a : ∀ x, Numbering (A x)) (q : ∀ x, Numbering (Q x)) (i : Numbering I)
  (ha : Computable fun x => (a x).size) (hq : Computable fun x => (q x).size)
  (blank : ∀ x, A x) (hb : Computable fun x => ((a x).equiv (blank x)).val)
  (rows : ℕ → ℕ × ℕ → Option (ℕ × ℕ)) (hrws : Computable₂ rows)
  (machine : ∀ x, TM.Rule (A x) (Q x) I)
  (hcorrect : ∀ x z r, rows x (((q x).equiv z).val, (i.arrow (a x) |>.equiv r).val) =
    (machine x z r).map (fun v => (((q x).equiv v.1).val,
      (i.arrow ((a x).prod Numbering.move) |>.equiv v.2).val)))
set_option quotPrecheck false
local notation "p" => states a q i (fun x => (a x).size) (ha := ha) (hq := hq) (hw := ha)
local notation "code" => fun x => oneHot (a x).equiv (blank x)
local notation "num" => fun x => Numbering.controller (a x) (q x) i (a x).size
include ha hq hrws hb hcorrect

/-- Construct the literal ROM emitted for a family with varying machine alphabets.
Both sides use the same program, state numbering and finite tuple enumeration. -/
theorem computable_program (entry : ∀ x, Q x)
    (he : Computable fun x => ((q x).equiv (entry x)).val)
    {M : ℕ} (enum : Universal.Tag (Option Bool) I ≃ Fin (M+1)) :
    Computable fun x => (Numbering.program (a x) (q x) i (code x) (machine x) (entry x)).map
      (fun t => (enum t).val) :=
  Generator.computable_numbered_program Numbering.ternary i num
    (fun x => readStart (code x) (entry x)) (fun x => CommonAlphabet.rule (code x) (machine x))
    (i.arrow Numbering.ternary).all enum (packed a q i ha hq blank rows)
    (p).size_eff (readStart_rank a q i ha hq code ha entry he) (computable_packed a q i ha hq blank hb rows hrws)
    (packed_correct a q i ha hq blank rows machine hcorrect)

end Generator.Phase

end NearSquareRoot
end Computability
end OAI
