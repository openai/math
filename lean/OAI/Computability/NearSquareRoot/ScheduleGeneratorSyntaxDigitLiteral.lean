import OAI.Computability.NearSquareRoot.FixedCandidateLiteral
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxDigitFamily

/-! # Local four-letter digit rules for the released multiplication candidate family -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.LiteralFamily

open IntegerMultiplication CommonAlphabet GeneratorSyntax.Pack

variable {T : ℕ → ℕ → ℕ} (f : LiteralFamily T)

/-- The private bank is independent of the candidate index. -/
abbrev digitBank := (GeneratorSyntax.Padding.fixed f.registers).option

abbrev digitCmd (j : ℕ) := multiplyWrap (f.cmd j)

noncomputable abbrev digitStates (j : ℕ) := digitNum f.registers (f.digitCmd j)
noncomputable abbrev digitStart (j : ℕ) := digitEntry f.registers (f.digitCmd j)
noncomputable abbrev digitRule (j : ℕ) :=
  digitMachine f.positive (f.digitCmd j) (within_multiplyWrap f.positive (f.bounded j))

/-- The released family supplies the addresses and physical rows of every
digit machine, together with the resources for the canonical product call. -/
theorem digits :
    Computable (fun j => (f.digitStates j).size) ∧
    Computable (fun j => ((f.digitStates j).equiv (f.digitStart j)).val) ∧
    Generator.EffectiveRows Numbering.publicLetter (Numbering.publicIndex f.digitBank)
      f.digitStates f.digitRule ∧
    ∀ j, ∃ E : ℕ, 0 < E ∧ StagingCall.Computes (f.digitRule j) (f.digitStart j) Lea.answer
      (fun n => E*(T j n+n+1)) (fun n => E*(n+1)) := by
  obtain ⟨size,start,rows,runs,_⟩ := digit_family f.positive f.cmd f.effective f.bounded T
    (fun _ => 21) f.coeff (fun _ i => Lea.answer i.operands) f.body
    (fun _ i => ⟨Lea.date_length _, Lea.value_answer i.val.property⟩)
  refine ⟨size,start,rows,fun j => ?_⟩
  obtain ⟨E,pos,run⟩ := runs j
  exact ⟨E,pos,fun v => by simpa only [digitProduct_val] using run v⟩

end FixedCandidate.LiteralFamily

end NearSquareRoot
end Computability
end OAI
