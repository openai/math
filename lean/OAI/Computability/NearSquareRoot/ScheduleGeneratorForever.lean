import OAI.Computability.NearSquareRoot.ScheduleGeneratorROMExecute
import OAI.Computability.NearSquareRoot.ScheduleGeneratorInputRun
import OAI.Computability.NearSquareRoot.ScheduleForever

/-! # Divergence through unary input, code generation and ROM dispatch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorPipeline
open IntegerMultiplication TM Turing Turing.ToPartrec Turing.PartrecToTM2 Universal
variable {A I : Type} {M : ℕ}

/-- Once a total generator emits the installed program, every unbounded family of
installer prefixes lifts to an unbounded family of physical pipeline prefixes. -/
theorem runsForever_of_loader [Finite A] [Fintype I] (blank : A) (c : Code)
    (enum : Tag A I ≃ Fin (M+1)) (w : List ℕ) (v : List (Tag A I))
    (hcode : symbolWord enum v ∈ c.eval w) (d : I → Tape A)
    (live : RunsForever (Loader.installAndRun blank)
      (TapeSequence.relabel Sum.inl (Loader.initial blank v d))) :
    RunsForever (rule blank c enum) (initial blank c w d) := by
  obtain ⟨g,prepares⟩ := prepare_run blank c enum w v hcode
  obtain ⟨a,first,halt,layout⟩ := prepares d
  let boot : Config (Letter A I) (Loader.Control ⊕ PC) (Universal.Index I) :=
    TapeSequence.relabel Sum.inl (Loader.initial blank v d)
  let onBank := CommonTapes.config loaderIndex a.tape (Q := Loader.Control ⊕ PC)
  have mounted : onBank boot = ⟨.inl .copy,a.tape⟩ := by
    apply congrArg (Config.mk _)
    funext j
    cases j with
    | inl k => exact CommonTapes.extend_off _ _ _ _ (by rintro ⟨j,h⟩; contradiction)
    | inr j =>
      change CommonTapes.extend loaderIndex _ _ (loaderIndex j) = _
      rw [CommonTapes.extend_apply]
      exact (layout j).symm
  apply runsForever_of_long
  intro n
  obtain ⟨z,hz⟩ := live n
  have second : Trace (advance (execute blank)) (onBank boot) n (onBank z) :=
    CommonTapes.trace _ _ _ hz
  rw [mounted] at second
  have switched := (TapeSequence.first_trace _ (execute blank) (.inl .copy) first).trans
    (.single (TapeSequence.handoff _ _ _ halt))
  exact ⟨g+1+n,by omega,_,switched.trans (TapeSequence.second_trace _ _ _ second)⟩

end GeneratorPipeline

namespace GeneratorInputRun
open IntegerMultiplication TM Turing.ToPartrec Turing.PartrecToTM2 Universal
variable {A I : Type} {M : ℕ}

theorem runsForever_of_pipeline [Finite A] [Fintype I] (blank : A) (mark : Letter A I)
    (distinct : Sum.inl blank ≠ mark) (c : Code) (enum : Tag A I ≃ Fin (M+1))
    (H : ℤ) (j : ℕ) (d : I → Tape A)
    (live : RunsForever (GeneratorPipeline.rule blank c enum)
      (GeneratorPipeline.initial blank c (Generator.unaryInput j) d)) :
    RunsForever (rule blank mark c enum) (initial blank mark c H j d) := by
  apply runsForever_of_long
  intro n
  obtain ⟨z,tr⟩ := live n
  exact ⟨_,by omega,_,run_prefix blank mark distinct c enum H j d tr⟩

end GeneratorInputRun

end NearSquareRoot
end Computability
end OAI
