import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxFamily
import OAI.Computability.NearSquareRoot.ScheduleGeneratorPublicProgram

/-! # Public bit-input and bit-output ROM for P192 tree-stack commands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack
open IntegerMultiplication CommonAlphabet

variable [Fintype IntegerMultiplication.Code.Ltr] {R : ℕ}

/-- The common register embedding sends source register zero to this tape. -/
def fixedInput (hR : 0 < R) : Option (Option (Fin R)) := some (some ⟨0,hR⟩)

theorem fixedInput_eq (hR : 0 < R) (p : IntegerMultiplication.Code.Cmd)
    (bound : CommonRegisters.Within R p) :
    CommonRegisters.indexEmbedding hR bound (inputTape p) = fixedInput hR := rfl

/-- Installable ROM that accepts literal bits with their public separator and
writes literal output bits. Input expansion and head realignment are in the ROM. -/
noncomputable def publicROM (hR : 0 < R) (p : IntegerMultiplication.Code.Cmd)
    (bound : CommonRegisters.Within R p) :=
  let a := dataNum ltrNumbering p
  let bit := fun v => symbol p (.bit v)
  Pipeline.sourceProgram a (controlNum ltrNumbering p) (Padding.fixed R) (oneHot a.equiv none)
    bit (symbol p .sep) (Generator.PublicProgram.decode a bit) (fixedInput hR) none
    (paddedRule hR p bound) (entry p)

/-- Instantiation at the actual P192 command alphabet, including all literal
input and output transitions, from computable syntax alone. -/
theorem computable_publicROM (hR : 0 < R) (p : ℕ → IntegerMultiplication.Code.Cmd)
    (eff : Effective ltr p) (bound : ∀ j, CommonRegisters.Within R (p j)) {M : ℕ}
    (enum : Universal.Tag Public.Letter (Pipeline.Index (Option (Option (Option (Fin R))))) ≃ Fin (M+1)) :
    Computable fun j => (publicROM hR (p j) (bound j)).map (fun t => (enum t).val) := by
  obtain ⟨ha,hq,he,rows,hr,correct⟩ := paddedRows ltrNumbering hR p eff bound
  have literal (v : IntegerMultiplication.Code.Ltr) :
      Computable fun j => ((dataNum ltrNumbering (p j)).equiv (symbol (p j) v)).val := by
    simp only [symbol_rank]
    exact Computable.const _
  have blank : Computable fun j => ((dataNum ltrNumbering (p j)).equiv none).val := by
    simp only [blank_rank]
    exact Computable.const 0
  exact Generator.PublicProgram.computable_rom (fun j => dataNum ltrNumbering (p j))
    (fun j => controlNum ltrNumbering (p j)) (Padding.fixed R)
    (fun j v => symbol (p j) (.bit v)) (fun j => symbol (p j) .sep) (fun _ => none)
    (fixedInput hR) none (fun j => paddedRule hR (p j) (bound j)) (fun j => entry (p j)) enum
    ha hq (literal (.bit false)) (literal (.bit true)) (literal .sep) blank he rows hr correct

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
