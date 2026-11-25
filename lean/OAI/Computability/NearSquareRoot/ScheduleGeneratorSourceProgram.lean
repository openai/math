import OAI.Computability.NearSquareRoot.ScheduleGeneratorAlignRows
import OAI.Computability.NearSquareRoot.ScheduleGeneratorPipelineRows
import OAI.Computability.NearSquareRoot.ScheduleGeneratorPhase
import OAI.Computability.NearSquareRoot.CommonAlphabetIOPipelineSource

/-! # Uniform ROM generation for a machine with physical public input and output -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator
open CommonAlphabet IntegerMultiplication TM

namespace EffectiveRows

/-- Extend every row with the folded distance tape and its return-to-origin transitions. -/
theorem align {A I : Type} {Q : ℕ → Type} [DecidableEq A] [DecidableEq I]
    {a : Numbering A} {i : Numbering I} {q : ∀ j, Numbering (Q j)}
    {m : ∀ j, Rule A (Q j) I} (base : EffectiveRows a i q m)
    (out : I) (blank marker : A) (entry : ∀ j, Q j)
    (size : Computable fun j => (q j).size) (start : Computable fun j => ((q j).equiv (entry j)).val) :
    EffectiveRows a i.option (fun j => (q j).align)
      (fun j => Align.rule out blank marker (entry j) (m j)) := by
  obtain ⟨f,hf,hm⟩ := base
  exact ⟨Alignment.rows a i out blank marker _ _ f,
    Alignment.computable_rows a i out blank marker size start hf,
    Alignment.rows_correct a i out blank marker q entry m f hm⟩

end EffectiveRows

namespace PipelineRows
variable {A Q : ℕ → Type} {I : Type} [DecidableEq I]
variable (a : ∀ j, Numbering (A j)) (q : ∀ j, Numbering (Q j)) (i : Numbering I)
    (c : ∀ j, Code (A j)) (bit : ∀ j, Bool → A j) (sep : ∀ j, A j)
    (decode : ∀ j, A j → Option Bool) (inp out : I) (m : ∀ j, Rule (A j) (Q j) I) (entry : ∀ j, Q j)

private abbrev controlNum (j : ℕ) := Numbering.controller (a j) (q j) i (c j).width
local notation "ctrl" => controlNum a q i c

/-- The ranked ROM of the physical pipeline is one computable sequence of finite words.
The same `sourceProgram` is used by the interpreter's `installed_from_source` theorem. -/
theorem computable_sourceProgram {M : ℕ}
    (enum : Universal.Tag Public.Letter (Pipeline.Index (Option I)) ≃ Fin (M+1))
    (ha : Computable fun j => (a j).size) (hq : Computable fun j => (q j).size)
    (hw : Computable fun j => (c j).width)
    (hstart : Computable fun j => ((ctrl j).equiv (readStart (c j) (entry j))).val)
    (base : EffectiveRows Numbering.ternary i ctrl (fun j => CommonAlphabet.rule (c j) (m j)))
    (expand : EffectiveRows Numbering.publicLetter Numbering.bool
      (fun j => Numbering.expand (a j) (c j).width)
      (fun j => Expand.rule (c j) (Public.parse (bit j) (sep j)) Public.emb))
    (compact : EffectiveRows Numbering.publicLetter Numbering.bool (fun j => Numbering.compact (c j).width)
      (fun j => Compact.rule (c j) Pipeline.digit (decode j) Public.bit Option.isNone)) :
    Computable fun j =>
      (Pipeline.sourceProgram (a j) (q j) i (c j) (bit j) (sep j) (decode j) inp out (m j) (entry j)).map
        (fun t => (enum t).val) := by
  let u := ctrl
  have hctrl : Computable fun j => (u j).size := (Phase.states a q i (fun j => (c j).width) ha hq hw).size_eff
  have halign := computable_align_size u hctrl
  have core := (base.commonBlank Numbering.publicLetter (fun _ => (none : Option Bool))).align
    out (none : Public.Letter) Public.sep (fun j => readStart (c j) (entry j)) hctrl hstart
  have all := effective_pipeline a (fun j => (u j).align) i.option c bit sep decode
    (some inp) (some out) _ (fun _ => .boot) ha halign hw (Computable.const 0) expand core compact
  exact computable_program a (fun j => (u j).align) i.option c bit sep decode
    (some inp) (some out) _ (fun _ => .boot) enum ha halign hw all

end PipelineRows
end Generator

end NearSquareRoot
end Computability
end OAI
