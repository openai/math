import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagedPrelude
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagingSerializeRows
import OAI.Computability.NearSquareRoot.ScheduleGeneratorIndexedRules
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxDigitLiteral

/-! # Effective rows of the complete positive branch with the paper's index convention -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Staged
open CommonAlphabet IntegerMultiplication TM ChunkControl
noncomputable section

variable {I : Type} [Fintype I] [DecidableEq I] {Q : ℕ → Type} (d : Driver)
    [DecidableEq (StagingControl.Letter d)] (C : ℕ)
variable (i : CommonAlphabet.Numbering I) (q : ∀ j, Numbering (Q j))
    (g : ∀ j, Rule Public.Letter (Q j) (Pipeline.Index I)) (e : ∀ j, Q j)

abbrev positiveStates (l : ℕ) :=
  (preNum (StagingWidth.Phase C) (IndexedRules.split l)).sum
    (states (I:=I) d q (IndexedRules.template l))

def positive (l : ℕ) := StagingStartup.machine d (IndexedRules.split l) C
  (StagingReject.successful d (g (IndexedRules.template l)) (e (IndexedRules.template l)))
  (entry (I:=I) d (Q (IndexedRules.template l)))

def positiveStart (l : ℕ) : StagingStartup.PC (IndexedRules.split l) (StagingWidth.Phase C) ⊕
    StagingProtection.State d (StagingDigit.PC (Q (IndexedRules.template l)) I) :=
  .inl (StagingStartup.start (IndexedRules.split l))

omit [DecidableEq I] [DecidableEq (StagingControl.Letter d)] in
theorem positive_size (hq : Computable fun j => (q j).size) :
    Computable fun l => (positiveStates (I:=I) d C q l).size :=
  Primrec.nat_add.to_comp.comp (preSize.comp IndexedRules.computable_split)
    ((size d q hq).comp IndexedRules.computable_template)

omit [DecidableEq I] [DecidableEq (StagingControl.Letter d)] in
theorem positive_start :
    Computable fun l => ((positiveStates (I:=I) d C q l).equiv (positiveStart (I:=I) (Q:=Q) d C l)).val :=
  (Computable.const 9).of_eq fun l => by
    change 9 = SerializeRows.rank (StagingSerialize.start (IndexedRules.split l))
    exact (SerializeRows.rank_start _).symm

/-- The serializer checks the exponent on the literal operand, constructs its register
stream, paints the fences, then hands off to the repeated guarded digit calls. -/
theorem positive_rows (hq : Computable fun j => (q j).size)
    (he : Computable fun j => ((q j).equiv (e j)).val)
    (hg : EffectiveRows Numbering.publicLetter (Numbering.publicIndex i) q g) :
    EffectiveRows (num (StagingProtection.Cell d)) (tapeNum d I) (positiveStates d C q)
      (positive d C g e) := by
  let a := num (StagingProtection.Cell d)
  have prep := (preRows (I:=I) d a (SerializeRows.rows d a) (StagingWidth.rule d C)
    (StagingWidth.start C) (StagingWidth.delimiter d)).reindex _ IndexedRules.computable_split
  have run := ((successful_rows d i q g e hq he hg).route (Pipeline.coreRoute _) (tapeNum d I)).reindex _
    IndexedRules.computable_template
  exact prep.seq run (preSize.comp IndexedRules.computable_split)
    (fun l => entry (I:=I) d (Q (IndexedRules.template l))) ((start d q).comp IndexedRules.computable_template)

end
end Generator.Staged

end NearSquareRoot
end Computability
end OAI
