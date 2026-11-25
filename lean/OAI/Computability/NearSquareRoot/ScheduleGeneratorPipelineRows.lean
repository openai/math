import OAI.Computability.NearSquareRoot.ScheduleGeneratorSequenceRows
import OAI.Computability.NearSquareRoot.CommonAlphabetIOPipelineROM
import OAI.Computability.NearSquareRoot.KernelComputableAddress

/-! # A single computably generated ROM for consecutive public input, execution and output -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator
open CommonAlphabet IntegerMultiplication TM

namespace PipelineRows

/-- The expansion control has three nullary phases, one position loop, and one letter
and position for the emission loop. -/
theorem expand_size {A : Type} (a : Numbering A) (w : ℕ) :
    (Numbering.expand a w).size = (a.size*w+w)+1+1+1 := rfl

theorem compact_size (w : ℕ) :
    (Numbering.compact w).size = 3^w*w+(3+w)+1+1 := rfl

theorem align_size {Q : Type} (q : Numbering Q) :
    q.align.size = q.size*2+2+1+1 := rfl

theorem expand_entry {A : Type} (a : Numbering A) (w : ℕ) :
    ((Numbering.expand a w).equiv .scan).val = 0 := rfl

theorem compact_entry {A : Type} (c : Code A) :
    ((Numbering.compact c.width).equiv (Compact.start c)).val = 2 := by
  have h : (finFunctionFinEquiv (fun _ : Fin c.width => (0 : Fin 3))).val = 0 := by
    rw [finFunctionFinEquiv_apply]
    simp
  change (0 + c.width*(finFunctionFinEquiv (fun _ : Fin c.width => (0 : Fin 3))).val)+1+1 = 2
  rw [h,Nat.mul_zero,Nat.zero_add]

variable {A Q : ℕ → Type} {I : Type} [DecidableEq I]
variable (a : ∀ j, Numbering (A j)) (q : ∀ j, Numbering (Q j)) (i : Numbering I)
variable (c : ∀ j, Code (A j)) (srcBit : ∀ j, Bool → A j) (srcSep : ∀ j, A j)
    (decode : ∀ j, A j → Option Bool) (inp out : I) (m : ∀ j, Rule Public.Letter (Q j) I)
    (entry : ∀ j, Q j)

theorem computable_expand_size (ha : Computable fun j => (a j).size)
    (hw : Computable fun j => (c j).width) :
    Computable fun j => (Numbering.expand (a j) (c j).width).size :=
  Primrec.succ.to_comp.comp (Primrec.succ.to_comp.comp (Primrec.succ.to_comp.comp
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp ha hw) hw)))

theorem computable_compact_size (hw : Computable fun j => (c j).width) :
    Computable fun j => (Numbering.compact (c j).width).size :=
  Primrec.succ.to_comp.comp (Primrec.succ.to_comp.comp (Primrec.nat_add.to_comp.comp
    (Primrec.nat_mul.to_comp.comp ((KernelComputableAddress.primrec_pow (Primrec.const 3) (Primrec.id (α := ℕ))).to_comp.comp hw) hw)
    (Primrec.nat_add.to_comp.comp (Computable.const 3) hw)))

theorem computable_align_size (hq : Computable fun j => (q j).size) :
    Computable fun j => (q j).align.size :=
  Primrec.succ.to_comp.comp (Primrec.succ.to_comp.comp (Primrec.nat_add.to_comp.comp
    (Primrec.nat_mul.to_comp.comp hq (Computable.const 2)) (Computable.const 2)))

/-- The numerical transition of the whole public shell follows from its three local
transitions. All inactive tapes and both charged handoffs are part of that transition. -/
theorem effective_pipeline (ha : Computable fun j => (a j).size)
    (hq : Computable fun j => (q j).size) (hw : Computable fun j => (c j).width)
    (he : Computable fun j => ((q j).equiv (entry j)).val)
    (expand : EffectiveRows Numbering.publicLetter Numbering.bool
      (fun j => Numbering.expand (a j) (c j).width)
      (fun j => Expand.rule (c j) (Public.parse (srcBit j) (srcSep j)) Public.emb))
    (middle : EffectiveRows Numbering.publicLetter i q m)
    (compact : EffectiveRows Numbering.publicLetter Numbering.bool (fun j => Numbering.compact (c j).width)
      (fun j => Compact.rule (c j) Pipeline.digit (decode j) Public.bit Option.isNone)) :
    EffectiveRows Numbering.publicLetter (Numbering.publicIndex i)
      (fun j => Numbering.pipeline (a j) (q j) (c j).width)
      (fun j => Pipeline.machine (c j) (srcBit j) (srcSep j) (decode j) inp out (m j) (entry j)) := by
  let tape := Numbering.publicIndex i
  have xs := computable_expand_size a c ha hw
  have first := (expand.route (Pipeline.inputRoute inp) tape).seq
    (middle.route (Pipeline.coreRoute I) tape) xs entry he
  have total := Primrec.nat_add.to_comp.comp xs hq
  exact first.seq (compact.route (Pipeline.outputRoute out) tape) total (fun j => Compact.start (c j))
    ((Computable.const 2).of_eq fun j => (compact_entry (c j)).symm)

/-- The natural labels of the installed ROM form a computable function of the
candidate index. The read table enumerates every joint four-letter head observation. -/
theorem computable_program {M : ℕ} (enum : Universal.Tag Public.Letter (Pipeline.Index I) ≃ Fin (M+1))
    (ha : Computable fun j => (a j).size) (hq : Computable fun j => (q j).size)
    (hw : Computable fun j => (c j).width)
    (rows : EffectiveRows Numbering.publicLetter (Numbering.publicIndex i)
      (fun j => Numbering.pipeline (a j) (q j) (c j).width)
      (fun j => Pipeline.machine (c j) (srcBit j) (srcSep j) (decode j) inp out (m j) (entry j))) :
    Computable fun j =>
      (Pipeline.program (a j) (q j) i (c j) (srcBit j) (srcSep j) (decode j) inp out (m j) (entry j)).map
        (fun t => (enum t).val) := by
  obtain ⟨ev,he,hv⟩ := rows
  apply computable_numbered_program Numbering.publicLetter (Numbering.publicIndex i) _ _ _ _ enum ev
    (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp (computable_expand_size a c ha hw) hq)
      (computable_compact_size c hw)) (Computable.const 0) he hv

end PipelineRows
end Generator

end NearSquareRoot
end Computability
end OAI
