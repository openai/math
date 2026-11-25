import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagingOutput
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagingDigit
import OAI.Computability.NearSquareRoot.ScheduleStagingFamily

/-! # Literal transition-table generation for protected split candidates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Staged
open CommonAlphabet IntegerMultiplication TM ChunkControl

noncomputable section

variable {I : Type} [Fintype I] [DecidableEq I] {Q : ℕ → Type} (d : Driver)

abbrev num := StagedDigit.fixed

abbrev states (q : ∀ j, Numbering (Q j)) (j : ℕ) :
    Numbering (StagingProtection.State d (StagingDigit.PC (Q j) I)) :=
  Numbering.bool.prod (((num (StagingControl.State d)).sum (StagedDigit.states q j)).option)

def entry (Q : Type) : StagingProtection.State d (StagingDigit.PC Q I) :=
  (false,some (.inl (.inl (ChunkDispatch.start (StagingOpen.cmd d) .load))))

omit [Fintype I] [DecidableEq I] in
@[simp] theorem entry_eq (Q : Type) (C n : ℕ) (s : List Code.Ltr) :
    (StagingProtection.initial (D:=StagingDigit.PC Q I) (I:=I) d C n s).pc = entry (I:=I) d Q := rfl

variable (i : CommonAlphabet.Numbering I) (q : ∀ j, Numbering (Q j))
    (g : ∀ j, Rule Public.Letter (Q j) (Pipeline.Index I)) (e : ∀ j, Q j)

omit [DecidableEq I] in
theorem size (hq : Computable fun j => (q j).size) :
    Computable fun j => (states (I:=I) d q j).size :=
  EffectiveRows.size_fenced_publication <|
    Primrec.nat_add.to_comp.comp (Computable.const _) (StagedDigit.size (I:=I) q hq)

omit [DecidableEq I] in
theorem start : Computable fun j => ((states d q j).equiv (entry (I:=I) d (Q j))).val :=
  EffectiveRows.entry_fenced_publication _ (Computable.const _)

/-- The protected stage's actual transition function has uniformly computable numerical rows.
The controller axis and cell alphabet depend on the fixed driver alone. -/
theorem rows (hq : Computable fun j => (q j).size)
    (he : Computable fun j => ((q j).equiv (e j)).val)
    (hg : EffectiveRows Numbering.publicLetter (Numbering.publicIndex i) q g) :
    EffectiveRows (num (StagingProtection.Cell d)) (num (StagingOuter.Axis d I)).option.option
      (states d q) (fun j => StagingProduct.guarded d (g j) (e j)) := by
  let : DecidableEq (StagingControl.Letter d) := Classical.decEq _
  let : Fintype (StagingOuter.Axis d I) := Fintype.ofFinite _
  let al := num (StagingOuter.Letter d)
  let ix := num (StagingOuter.Axis d I)
  let ct := num (StagingControl.State d)
  let dt := StagedDigit.states (I:=I) q
  let digit := fun j => StagingProduct.digit d (g j) (e j)
  have digitRows : EffectiveRows al ix dt digit := StagedDigit.rows q al i ix (StagingOpen.one d)
    (StagingLetters.encoding d) (StagingLetters.sentinel d) (StagingLetters.reserved d) g e hg hq he
  have cycle := EffectiveRows.cycle al ix ct dt (StagingOuter.controller d) digit
    (fun _ => StagingDigit.start) (.inl (ChunkDispatch.start (StagingOpen.cmd d) .collect))
    (StagingControl.digit d) (StagedDigit.start q) digitRows
  have pub := cycle.publish (StagingOuterOutput.source d) (StagingOuterOutput.decode d) (StagingOuterOutput.bit d)
  have fullSize : Computable fun j => ((ct.sum (dt j)).option).size :=
    Primrec.succ.to_comp.comp (Primrec.nat_add.to_comp.comp (Computable.const _) (StagedDigit.size q hq))
  exact (pub.fence (num (StagingProtection.Cell d)) fullSize).mirror (StagingProtection.clean d) none

/-- A single number-valued evaluator emits every tag of the full protected ROM. -/
theorem computable_rom {M : ℕ} (enum : Universal.Tag (StagingProtection.Cell d)
    (StagingProtection.Tapes d I) ≃ Fin (M+1))
    (hq : Computable fun j => (q j).size) (he : Computable fun j => ((q j).equiv (e j)).val)
    (hg : EffectiveRows Numbering.publicLetter (Numbering.publicIndex i) q g) :
    Computable fun j => (Universal.Reindex.encode ((states d q j).equiv) (entry (I:=I) d (Q j))
      (StagingProduct.guarded d (g j) (e j))
      (((num (StagingOuter.Axis d I)).option.option.arrow (num (StagingProtection.Cell d))).all)).map
        (fun tag => (enum tag).val) := by
  obtain ⟨r,hr,rc⟩ := rows d i q g e hq he hg
  exact computable_numbered_program _ _ _ _ _ _ enum r (size d q hq) (start d q) hr rc

end
end Generator.Staged

end NearSquareRoot
end Computability
end OAI
