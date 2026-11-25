import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagedPositive
import OAI.Computability.NearSquareRoot.ScheduleGeneratorCandidate
import OAI.Computability.NearSquareRoot.ScheduleStagingFallbackLayout

/-! # The indexed candidate source consumed by the physical race -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Staged
open CommonAlphabet IntegerMultiplication TM ChunkControl GeneratorInputRun
noncomputable section

variable {I F : Type} [Fintype I] [DecidableEq I] [Finite F] {Q : ℕ → Type}
    (d : Driver) [DecidableEq (StagingControl.Letter d)] (C : ℕ)
variable (i : CommonAlphabet.Numbering I) (q : ∀ j, Numbering (Q j))
    (g : ∀ j, Rule Public.Letter (Q j) (Pipeline.Index I)) (e : ∀ j, Q j)
    (fallback : Rule (StagingProtection.Cell d) F (StagingFallback.Axes d I)) (f : F)

abbrev fullStates (l : ℕ) := IndexedRules.states (num F) (positiveStates (I:=I) d C q) l

def fullFast (l : ℕ) := (StagingFallback.positiveRoute d I).rule (positive d C g e l)

/-- The zero program and every successor have separate finite controls, but their
transitions use a single fixed alphabet, physical tape bank and read order. -/
def withFallback : Programs (StagingProtection.Cell d) (StagingFallback.Axes d I) where
  Q := IndexedRules.State F (fun l => StagingStartup.PC (IndexedRules.split l) (StagingWidth.Phase C) ⊕
    StagingProtection.State d (StagingDigit.PC (Q (IndexedRules.template l)) I))
  count l := (fullStates (I:=I) (F:=F) d C q l).size
  stateNumber l := (fullStates (I:=I) (F:=F) d C q l).equiv
  entry := IndexedRules.entry f (positiveStart (I:=I) (Q:=Q) d C)
  machine := IndexedRules.rule fallback (fullFast d C g e)
  reads := ((num (StagingFallback.Axes d I)).arrow (num (StagingProtection.Cell d))).all
  complete := ((num (StagingFallback.Axes d I)).arrow (num (StagingProtection.Cell d))).mem_all

theorem effective_withFallback {M : ℕ}
    (enum : Universal.Tag (StagingProtection.Cell d) (StagingFallback.Axes d I) ≃ Fin (M+1))
    (hq : Computable fun j => (q j).size) (he : Computable fun j => ((q j).equiv (e j)).val)
    (hg : EffectiveRows Numbering.publicLetter (Numbering.publicIndex i) q g) :
    Computable fun l => GeneratorPipeline.symbolWord enum ((withFallback d C q g e fallback f).code l) := by
  let a := num (StagingProtection.Cell d)
  let k := num (StagingFallback.Axes d I)
  let rs := (k.arrow a).all
  let count := positiveStates (I:=I) d C q
  let begin := positiveStart (I:=I) (Q:=Q) d C
  let fast := fullFast d C g e
  obtain ⟨r,hr,correct⟩ := (positive_rows d C i q g e hq he hg).route (StagingFallback.positiveRoute d I) k
  have eff := computable_numbered_program a k count begin fast rs enum r (positive_size d C q hq)
    (positive_start (I:=I) d C q) hr correct
  exact (IndexedRules.emit fallback fast enum rs (num F) count f begin eff).1

end
end Generator.Staged

end NearSquareRoot
end Computability
end OAI
