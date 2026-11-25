import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxDigit

/-! # Numerically effective physical rows of a family of digit commands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack
open IntegerMultiplication CommonAlphabet
open IntegerMultiplication.Code (Cmd Ltr)

variable [Fintype Ltr] {R : ℕ}

/-- The local rule's actual control numbering gives both its serialized row
addresses and the computable number of rows needed by a caller. -/
theorem digitRows (hR : 0 < R) (p : ℕ → Cmd) (eff : Effective ltr p)
    (bound : ∀ j, CommonRegisters.Within R (p j)) :
    Computable (fun j => (digitNum R (p j)).size) ∧
    Computable (fun j => ((digitNum R (p j)).equiv (digitEntry R (p j))).val) ∧
    Generator.EffectiveRows Numbering.publicLetter (digitIndexNum R) (fun j => digitNum R (p j))
      (fun j => digitMachine hR (p j) (bound j)) := by
  obtain ⟨ha,hq,he,rows,hr,correct⟩ := paddedRows ltrNumbering hR p eff bound
  have literal (v : Ltr) :
      Computable fun j => ((dataNum ltrNumbering (p j)).equiv (symbol (p j) v)).val := by
    simp only [symbol_rank]
    exact Computable.const _
  have blank : Computable fun j => ((dataNum ltrNumbering (p j)).equiv none).val := by
    simp only [blank_rank]
    exact Computable.const 0
  refine ⟨computable_digitSize hR p eff bound,(Computable.const 0).of_eq (fun j => (digitEntry_rank R (p j)).symm),?_⟩
  exact Generator.PublicProgram.effective_rows (fun j => dataNum ltrNumbering (p j))
    (fun j => controlNum ltrNumbering (p j)) (Padding.fixed R)
    (fun j v => symbol (p j) (.bit v)) (fun j => symbol (p j) .sep) (fun _ => none)
    (fixedInput hR) none (fun j => paddedRule hR (p j) (bound j)) (fun j => entry (p j))
    ha hq (literal (.bit false)) (literal (.bit true)) (literal .sep) blank he rows hr correct

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
