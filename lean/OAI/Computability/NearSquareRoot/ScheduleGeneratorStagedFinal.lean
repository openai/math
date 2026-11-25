import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagedPrograms
import OAI.Computability.NearSquareRoot.ScheduleStagingFallback
import OAI.Computability.NearSquareRoot.ScheduleStagingStartupCandidate
import OAI.Computability.NearSquareRoot.FixedCandidateArenaLiteral

/-! # Literal programs for the fallback and every positive pair of parameters -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Staged
open CommonAlphabet IntegerMultiplication TM ChunkControl GeneratorInputRun
noncomputable section

private def fallbackNum : Numbering StagingFallback.PC :=
  let a := num StagingFallback.school.A
  let w := StagingFallback.code.width
  Numbering.pipeline a (Numbering.controller a (num StagingFallback.school.Q) (num StagingFallback.school.I) w).align w

local instance : Finite StagingFallback.PC :=
  Finite.of_injective fallbackNum.equiv fallbackNum.equiv.injective

variable {I : Type} [Fintype I] [DecidableEq I] {Q : ℕ → Type}
    (d : Driver) (C : ℕ)
local instance : DecidableEq (StagingControl.Letter d) := Classical.decEq _
variable (i : CommonAlphabet.Numbering I) (q : ∀ j, Numbering (Q j))
    (g : ∀ j, Rule Public.Letter (Q j) (Pipeline.Index I)) (e : ∀ j, Q j)

def programs : Programs (StagingProtection.Cell d) (StagingFallback.Axes d I) :=
  withFallback d C q g e (StagingFallback.machine d I) StagingFallback.start

@[simp] theorem programs_zero :
    (programs d C q g e).machine 0 = StagingFallback.machine d I := rfl

@[simp] theorem programs_succ (l : ℕ) :
    (programs d C q g e).machine (l+1) = (StagingFallback.positiveRoute d I).rule
      (StagingStartupCandidate.rule d (IndexedRules.split l) C (g (IndexedRules.template l))
        (e (IndexedRules.template l))) := rfl

@[simp] theorem entry_zero : (programs d C q g e).entry 0 = StagingFallback.start := rfl

@[simp] theorem entry_succ (l : ℕ) :
    (programs d C q g e).entry (l+1) = StagingStartupCandidate.start (I:=I) (Q:=Q (IndexedRules.template l))
      d (IndexedRules.split l) C := rfl

theorem effective_programs {M : ℕ}
    (enum : Universal.Tag (StagingProtection.Cell d) (StagingFallback.Axes d I) ≃ Fin (M+1))
    (hq : Computable fun j => (q j).size) (he : Computable fun j => ((q j).equiv (e j)).val)
    (hg : EffectiveRows Numbering.publicLetter (Numbering.publicIndex i) q g) :
    Computable fun l => GeneratorPipeline.symbolWord enum ((programs d C q g e).code l) :=
  effective_withFallback d C i q g e (StagingFallback.machine d I) StagingFallback.start enum hq he hg

variable {T : ℕ → ℕ → ℕ}

abbrev literalPrograms (f : FixedCandidate.LiteralFamily T) (d : Driver) (C : ℕ) :=
  programs d C f.digitStates f.digitRule f.digitStart

theorem literalPrograms_effective (f : FixedCandidate.LiteralFamily T) (d : Driver) (C : ℕ)
    {M : ℕ} (enum : Universal.Tag (StagingProtection.Cell d)
      (StagingFallback.Axes d (Option (GeneratorSyntax.Pack.FixedTapes f.registers))) ≃ Fin (M+1)) :
    Computable fun l => GeneratorPipeline.symbolWord enum ((literalPrograms f d C).code l) := by
  obtain ⟨hq,he,hg,_⟩ := f.digits
  exact effective_programs d C f.digitBank _ _ _ enum hq he hg

/-- The full proof uses this version when unselected arithmetic guesses may consume
a superlinear arena. Their finite controllers and generated rules have the same format. -/
abbrev arenaPrograms {S : ℕ → ℕ → ℕ} (f : FixedCandidate.ArenaFiles T S) (d : Driver) (C : ℕ) :=
  programs d C f.digitStates f.digitRule f.digitStart

theorem arenaPrograms_effective {S : ℕ → ℕ → ℕ} (f : FixedCandidate.ArenaFiles T S) (d : Driver) (C : ℕ)
    {M : ℕ} (enum : Universal.Tag (StagingProtection.Cell d)
      (StagingFallback.Axes d (Option (GeneratorSyntax.Pack.FixedTapes f.registers))) ≃ Fin (M+1)) :
    Computable fun l => GeneratorPipeline.symbolWord enum ((arenaPrograms f d C).code l) := by
  obtain ⟨hq,he,hg,_⟩ := f.digits
  exact effective_programs d C f.digitBank _ _ _ enum hq he hg

end
end Generator.Staged

end NearSquareRoot
end Computability
end OAI
