import OAI.Computability.NearSquareRoot.ScheduleGeneratorTemplateMachine
import OAI.Computability.NearSquareRoot.CommonAlphabetIOPipelineSource

/-! # A fixed executor for a computably presented family of source machines

The unary parameter selects a transition table. The public data tapes carry the
literal inputs, and the final public output head returns to zero. The simulation
constants may depend on the parameter and are uniform over source executions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorInputRun
open IntegerMultiplication TM CommonAlphabet

variable {A Q I : Type} [DecidableEq I] [Fintype I] {M : ℕ}

/-- Execute a source run on the public words and the raw unary parameter.
The output equality includes the tape head and every blank off the result. -/
def RunsSourceOnUnary (mark : Universal.Letter Public.Letter (Pipeline.Index (Option I)))
    (generator : Turing.ToPartrec.Code)
    (enum : Universal.Tag Public.Letter (Pipeline.Index (Option I)) ≃ Fin (M+1))
    (j : ℕ) (bit : Bool → A) (sep blank : A) (inp out : I)
    (source : Rule A Q I) (entry : Q) (E : ℕ) : Prop :=
  ∀ (H : ℤ) (x y z : List Bool) {t S : ℕ} (finish : Config A Q I),
    let start := loadedConfig entry blank (Pipeline.sourceLoad bit sep inp x y)
    Trace (advance source) start t finish → advance source finish = none →
    whole blank (z.map bit) (finish.tape out) → VisitsAtMost source start t S →
    let m := rule none mark generator enum
    let init := initial none mark generator H j (Pipeline.publicLoad x y)
    ∃ k stop, k ≤ E*(t+x.length+y.length+z.length+1) ∧ Trace (advance m) init k stop ∧
      advance m stop = none ∧ stop.tape (.inl ()) = Generator.Input.source (.inl none) mark H j ∧
      stop.tape (.inr (.inr (.inl (.inl true)))) =
        Tape.loaded (.inl none) (z.map fun b => .inl (Public.bit b)) ∧
      VisitsAtMost m init k (E*(S+x.length+y.length+z.length+1))

/-- A single program emits all the transition tables and executes their source
machines from ordinary unary and binary inputs. The source alphabets, controls
and block widths may vary with the parameter. -/
theorem source_family {A Q : ℕ → Type}
    (a : ∀ j, Numbering (A j)) (q : ∀ j, Numbering (Q j)) (i : Numbering I)
    (c : ∀ j, CommonAlphabet.Code (A j))
    (bit : ∀ j, Bool → A j) (sep blank : ∀ j, A j)
    (decode : ∀ j, A j → Option Bool) (inp out : I)
    (m : ∀ j, Rule (A j) (Q j) I) (entry : ∀ j, Q j)
    (hb : ∀ j, (c j).enc (blank j) = fun _ => none)
    (empty : ∀ j, decode j (blank j) = none)
    (digits : ∀ j b, decode j (bit j b) = some b)
    (mark : Universal.Letter Public.Letter (Pipeline.Index (Option I)))
    (distinct : Sum.inl none ≠ mark)
    (enum : Universal.Tag Public.Letter (Pipeline.Index (Option I)) ≃ Fin (M+1))
    (emits : Computable fun j =>
      (Pipeline.sourceProgram (a j) (q j) i (c j) (bit j) (sep j) (decode j)
        inp out (m j) (entry j)).map (fun t => (enum t).val)) :
    ∃ generator : Turing.ToPartrec.Code, Finite (Control generator M) ∧
      Finite (Index (Pipeline.Index (Option I))) ∧
      ∀ j, ∃ E : ℕ, 0 < E ∧ RunsSourceOnUnary mark generator enum j (bit j) (sep j) (blank j)
        inp out (m j) (entry j) E := by
  obtain ⟨generator,em⟩ := Generator.exists_unary_list_code _ emits
  let : Finite (GeneratorPipeline.Control generator M) := GeneratorPipeline.finite_control _ _
  let : Finite (GeneratorPipeline.Index (Pipeline.Index (Option I))) := GeneratorPipeline.finite_indices
  refine ⟨generator,inferInstance,inferInstance,fun j => ?_⟩
  let states := Numbering.pipeline (a j) (Numbering.controller (a j) (q j) i (c j).width).align
    (c j).width
  let reads := (Numbering.publicIndex i.option).arrow Numbering.publicLetter
  let pc := Pipeline.sourceEntry (A j) (Q j) I (c j).width
  let candidate := Pipeline.sourceMachine (c j) (bit j) (sep j) (decode j) inp out (m j) (entry j)
  obtain ⟨D,positive,runs⟩ := GeneratorPipeline.run_numbered none generator enum
    (Generator.unaryInput j) states.equiv pc candidate reads.all reads.mem_all (Part.eq_some_iff.mp (em j))
  let J := Fintype.card (Pipeline.Index (Option I))
  let B := D+8*j+18+2*(J+7)
  have unary : RunsOnUnary none mark generator enum j pc candidate B :=
    compile_unary none mark distinct generator enum j pc candidate D runs
  let F := 32*((c j).width+J+1)
  refine ⟨B*F,Nat.mul_pos (by dsimp [B]; omega) (by dsimp [F]; omega),?_⟩
  intro H x y z t S finish start tr halt output vis
  obtain ⟨steps,target,time,trace,done,word,cover⟩ :=
    Pipeline.literal_from_source (c j) (bit j) (sep j) (blank j) (hb j) (decode j)
      (empty j) (digits j) inp out (m j) (entry j) x y z finish tr halt output vis
  obtain ⟨k,stop,bound,exec,stops,restored,tapes,space⟩ :=
    unary H (Pipeline.publicLoad x y) trace done cover
  refine ⟨k,stop,bound.trans ?_,exec,stops,restored,?_,?_⟩
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    apply (Nat.add_le_add_right time 1).trans
    dsimp only [Pipeline.expandSteps,Pipeline.compactSteps,clock,F]
    ring_nf
    omega
  · rw [tapes,word,Pipeline.literal_data]
  · obtain ⟨cells,count,contains⟩ := space
    refine ⟨cells,count.trans ?_,contains⟩
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    dsimp only [Pipeline.expandSteps,Pipeline.compactSteps,F,J]
    ring_nf
    omega

end GeneratorInputRun

end NearSquareRoot
end Computability
end OAI
