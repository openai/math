import OAI.Computability.NearSquareRoot.ScheduleStagingLiteral
import OAI.Computability.NearSquareRoot.ScheduleStagingFallbackComparison
import OAI.Computability.NearSquareRoot.ScheduleStagingComparisonPositive
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagedFinal

/-! # Comparison certificates for the very same indexed programs whose ROMs are emitted -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Staged

open IntegerMultiplication TM CommonAlphabet Filter ScheduleMachine GeneratorInputRun
open ChunkControl (Driver)
open scoped Classical

noncomputable def coverage (d : Driver) (I : Type) (C : ℕ) :=
  max (StagingFallback.cells d I) (StagingComparisonPositive.D d I C)

private theorem enlarge {A Q I : Type} {m : Rule A Q I} {x t B n} (D : ℕ) (h : B ≤ D)
    (visited : VisitsAtMost m x t (B*(n+1))) : VisitsAtMost m x t (D*(n+1)) := by
  obtain ⟨v,size,cover⟩ := visited
  exact ⟨v,size.trans (Nat.mul_le_mul_right _ h),cover⟩

/-- The zero code is the ordinary polynomial multiplier. All positive codes
are sound. Each target exponent needs just one template with eventual
linear digit space and that exponent; the other templates can use arbitrary
space. The finite alphabet and the linear space coefficient are shared. -/
theorem comparisons {I : Type} [Fintype I] [DecidableEq I] {Q : ℕ → Type}
    (d : Driver) (C : ℕ) (ctl : StagingLiteral.Spec d C)
    (q : ∀ j, Numbering (Q j)) (g : ∀ j, Rule Public.Letter (Q j) (Pipeline.Index I)) (e : ∀ j, Q j)
    (T S : ℕ → ℕ → ℕ)
    (all : ∀ j, StagingCall.Computes (g j) (e j) Lea.answer (T j) (S j))
    (good : ∀ h : ℕ, ∃ (j L : ℕ) (A : ℝ), 0 ≤ A ∧
      (∀ᶠ n : ℕ in atTop, S (j+1) n ≤ L*(n+1)) ∧
      ∀ᶠ n : ℕ in atTop, (T (j+1) n : ℝ) ≤ A*n*logScale n^((1:ℝ)/2+1/(h+2:ℝ))) :
    (programs d C q g e).Comparisons (StagingFallback.ports d I) (coverage d I C) StagingFallback.time 2 := by
  let : DecidableEq (StagingControl.Letter d) := Classical.decEq _
  have width : StagingProduct.HasWidth Lea.answer := fun _ => Lea.date_length _
  have correct : StagingProduct.Multiplies Lea.answer := fun a => Lea.value_answer a.property.1
  refine ⟨?_,?_,?_⟩
  · intro i n x t y hist halt
    cases i with
    | zero => exact StagingFallback.sound d I n x hist halt
    | succ l =>
      obtain ⟨w,out,len,val⟩ := StagingComparisonPositive.sound d C g e l Lea.answer
        (T (IndexedRules.template l)) (S (IndexedRules.template l)) ctl (all _) width correct
        (xbits x) (ybits x) (by simp) hist halt
      exact ⟨w,⟨by simpa using len,val⟩,out⟩
  · intro n x
    obtain ⟨t,y,ht,run,halt,vis⟩ := StagingFallback.completes d I n x
    exact ⟨t,⟨y,run,halt,enlarge _ (Nat.le_max_left ..) vis⟩,ht⟩
  · intro h
    obtain ⟨j,L,A,hA,linear,time⟩ := good h
    obtain ⟨k,H,hH,late⟩ := StagingComparisonPositive.selected d C g e j Lea.answer
      (T (j+1)) (S (j+1)) ctl (all _) width correct L linear _ A (by positivity) hA time
    refine ⟨Nat.pair j k+1,H,hH,?_⟩
    filter_upwards [late] with n fit
    intro x
    obtain ⟨t,y,_,ht,path,halt,_,_,_,vis⟩ := fit (xbits x) (ybits x) (xbits_length x) (ybits_length x)
    exact ⟨t,⟨y,path.1,halt,enlarge _ (Nat.le_max_right ..) vis⟩,ht⟩

end Generator.Staged

end NearSquareRoot
end Computability
end OAI
