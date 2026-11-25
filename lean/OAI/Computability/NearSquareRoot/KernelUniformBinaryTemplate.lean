import OAI.Computability.NearSquareRoot.KernelComputableTemplateSearch
import OAI.Computability.NearSquareRoot.KernelPassComputableComposite
import OAI.Computability.NearSquareRoot.KernelPassLiteralProgram

/-! # A Turing-computable family of normalized, strictly saving templates

The returned arity and opcode list contain all control, parity masks and
signed dyadic coefficients. The selector has a single program for all
values of its input index. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax

theorem computable_templates (num den : ℕ → ℕ) (hnum : Primrec num) (hden : Primrec den)
    (hd : ∀ j, 0 < den j) (hθ : ∀ j, 1/2 < (num j : ℝ)/(den j)) :
    ∃ select : ℕ → Raw, Computable select ∧ ∀ j, (interpreted (select j)).Good (num j) (den j) :=
  select_of_evaluation (fun r h => compiledTable r.1 h r.2)
    (primrec_compiledTable (Primrec.fst.comp Primrec.fst) Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
    (fun r h => compiledTable_represents r.1 h r.2) num den hnum hden hd hθ

theorem midpoint_exponent (j : ℕ) :
    ((j+3 : ℕ) : ℝ) / (2*(j+2) : ℕ) = (1:ℝ)/2 + 1/(2*(j+2)) := by
  push_cast
  field_simp
  ring

/-- Use the exponent midway between a half and the scheduler target
`1/2 + 1/(j+2)`. The returned bytecode already contains the finite tables. -/
theorem computable_midpoint_templates :
    ∃ select : ℕ → Raw, Computable select ∧
      ∀ j, (interpreted (select j)).Good (j+3) (2*(j+2)) := by
  apply computable_templates (fun j => j+3) (fun j => 2*(j+2))
    (Primrec.nat_add.comp Primrec.id (Primrec.const 3))
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_add.comp Primrec.id (Primrec.const 2)))
  · intro j; omega
  · intro j
    rw [midpoint_exponent]
    have : (0:ℝ) < 1/(2*((j:ℝ)+2)) := by positivity
    linarith

/-- One four-tape generator writes the complete accepted arity and instruction
tables for every scheduler index, including the interpreter's actual visited
cells and halting computation. -/
theorem midpoint_template_generator :
    ∃ (s : ℕ → Raw) (c : Turing.ToPartrec.Code), Computable s ∧ ∀ j,
      (interpreted (s j)).Good (j+3) (2*(j+2)) ∧
      let w := Generator.unaryInput j
      let out := literalWord (s j)
      c.eval w = Part.some out ∧ ∃ t,
        IntegerMultiplication.Trace (IntegerMultiplication.TM.advance (Generator.rule c))
          (Generator.initial c w) t (Generator.finalCfg c w out) ∧
        IntegerMultiplication.TM.advance (Generator.rule c) (Generator.finalCfg c w out) = none ∧
        VisitsAtMost (Generator.rule c) (Generator.initial c w) t (4*(2*t+1)) := by
  obtain ⟨s,hs,hgood⟩ := computable_midpoint_templates
  obtain ⟨c,hc⟩ := literal_generator s hs
  exact ⟨s,c,hs,fun j => ⟨hgood j,hc j⟩⟩

end KernelPass.ComputableSyntax

end NearSquareRoot
end Computability
end OAI
