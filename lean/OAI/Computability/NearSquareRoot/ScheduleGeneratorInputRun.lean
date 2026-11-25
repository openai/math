import OAI.Computability.NearSquareRoot.ScheduleGeneratorInput
import OAI.Computability.NearSquareRoot.ScheduleGeneratorROMPipeline

/-!
# Starting the generator and interpreter from an ordinary unary tape

The extra tape holds the scheduler's unary index at an arbitrary address.
The adapter populates the generator's main tape, then a single transition
dispatches to the fixed generation, decoding and interpretation pipeline.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorInputRun
open IntegerMultiplication TM Universal Turing.ToPartrec Turing.PartrecToTM2
open Generator (unaryInput)
open scoped Classical
noncomputable section

variable {A I : Type} {M : ℕ}

abbrev Index (I : Type) := Unit ⊕ GeneratorPipeline.Index I
abbrev Control (c : Code) (M : ℕ) := Generator.Input.Control ⊕ GeneratorPipeline.Control c M

def copyIndex : Bool ↪ Index I :=
  ⟨fun b => if b then .inr (.inl .main) else .inl (),by
    intro x y eq
    cases x <;> cases y <;> simp_all⟩

def pipelineIndex : GeneratorPipeline.Index I ↪ Index I := Function.Embedding.inr

def copyRule (blank : A) (mark : Letter A I) : Rule (Letter A I) Generator.Input.Control (Index I) :=
  CommonTapes.rule copyIndex (Generator.Input.rule mark
    (GeneratorPipeline.source blank (some .cons)) (GeneratorPipeline.source blank (some .bit1)))

def pipelineRule [Finite A] [Finite I] (blank : A) (c : Code) (enum : Tag A I ≃ Fin (M+1)) :=
  CommonTapes.rule pipelineIndex (GeneratorPipeline.rule blank c enum)

def rule [Finite A] [Finite I] (blank : A) (mark : Letter A I) (c : Code)
    (enum : Tag A I ≃ Fin (M+1)) : Rule (Letter A I) (Control c M) (Index I) :=
  TapeSequence.rule (copyRule blank mark) (pipelineRule blank c enum)
    (.inl (.inl (Generator.initial c []).pc))

def unaryTapes (blank : A) (mark : Letter A I) (H : ℤ) (j : ℕ) (d : I → Tape A) :
    Index I → Tape (Letter A I) :=
  Sum.elim (fun _ => Generator.Input.source (.inl blank) mark H j) (GeneratorPipeline.inputTapes blank [] d)

def initial (blank : A) (mark : Letter A I) (c : Code) (H : ℤ) (j : ℕ) (d : I → Tape A) :
    Config (Letter A I) (Control c M) (Index I) :=
  ⟨.inl .copy,unaryTapes blank mark H j d⟩

/-- The pipeline's final control and every one of its tapes are preserved. -/
def finalCfg (blank : A) (mark : Letter A I) (H : ℤ) (j : ℕ) {c : Code}
    (z : Config (Letter A I) (GeneratorPipeline.Control c M) (GeneratorPipeline.Index I)) :
    Config (Letter A I) (Control c M) (Index I) :=
  ⟨.inr z.pc,Sum.elim (fun _ => Generator.Input.source (.inl blank) mark H j) z.tape⟩

private theorem map_loaded {B D : Type} (f : B → D) (blank : B) (xs : List B) :
    GeneratorPipeline.mapTape f (Tape.loaded blank xs) = Tape.loaded (f blank) (xs.map f) := by
  simp only [GeneratorPipeline.mapTape,Tape.loaded,Tape.mk.injEq,true_and]
  funext k
  cases k with
  | negSucc _ => rfl
  | ofNat n =>
    simp only [List.getElem?_map]
    cases xs[n]? <;> rfl

private theorem main_tape (blank : A) (j : ℕ) (d : I → Tape A) :
    GeneratorPipeline.inputTapes blank (unaryInput j) d (.inl .main) =
      Tape.loaded (.inl blank) (Generator.Input.word
        (GeneratorPipeline.source blank (some .cons)) (GeneratorPipeline.source blank (some .bit1)) j) := by
  dsimp only [GeneratorPipeline.inputTapes,Generator.inputTapes,Generator.stored,K'.elim]
  rw [map_loaded,List.map_map,Generator.Input.map_trList_input]
  rfl

private theorem idle {B J K : Type} (e : J ↪ K) (s : J → B) (old new : K → B)
    (on : ∀ j, s j = new (e j)) (off : ∀ k, (¬∃ j, e j = k) → old k = new k) :
    CommonTapes.extend e s old = new := by
  funext k
  by_cases h : ∃ j,e j = k
  · obtain ⟨j,rfl⟩ := h
    simpa using on j
  · rw [CommonTapes.extend_off _ _ _ _ h]
    exact off k h

private theorem pipeline_bank {B : Type} (source : Tape B) (bank : GeneratorPipeline.Index I → Tape B)
    (old : Index I → Tape B) (hc : old (.inl ()) = source) :
    CommonTapes.extend pipelineIndex bank old = Sum.elim (fun _ => source) bank := by
  apply idle
  · intro _; rfl
  · intro i h
    rcases i with _ | i
    · exact hc
    · exact (h ⟨i,rfl⟩).elim

private instance : Fintype K' := ⟨{.main,.rev,.aux,.stack},by intro k; cases k <;> simp⟩

/-- The finite unary adapter reaches the encoded generator input and returns the unary head. -/
theorem copy_phase [Fintype I] (blank : A) (mark : Letter A I) (distinct : Sum.inl blank ≠ mark)
    (c : Code) (H : ℤ) (j : ℕ) (d : I → Tape A) :
    let old := unaryTapes blank mark H j d
    let g := GeneratorPipeline.initial (M := M) blank c (unaryInput j) d
    ∃ f, Trace (advance (copyRule blank mark)) ⟨.copy,old⟩ (2*j+4) f ∧
      advance (copyRule blank mark) f = none ∧
      VisitsAtMost (copyRule blank mark) ⟨.copy,old⟩ (2*j+4) (8*j+18+Fintype.card (Index I)) ∧
      CommonTapes.config pipelineIndex old g = ⟨g.pc,f.tape⟩ := by
  let b : Letter A I := .inl blank
  let cons : Letter A I := GeneratorPipeline.source blank (some .cons)
  let one : Letter A I := GeneratorPipeline.source blank (some .bit1)
  let src := Generator.Input.source b mark H j
  let a := Generator.Input.pair .copy src (Tape.loaded b [])
  let f := Generator.Input.pair .done src (Tape.loaded b (Generator.Input.word cons one j))
  let pre := Generator.Input.rule mark cons one
  let old := unaryTapes blank mark H j d
  let aa := CommonTapes.config copyIndex old a
  let ff := CommonTapes.config copyIndex old f
  let g := GeneratorPipeline.initial (M := M) blank c (unaryInput j) d
  let gg := CommonTapes.config pipelineIndex old g
  have s₁ : Trace (advance (copyRule blank mark)) aa (2*j+4) ff :=
    CommonTapes.trace _ pre _ (Generator.Input.run b mark cons one H j distinct)
  have h₁ : advance (copyRule blank mark) ff = none := by
    change advance (CommonTapes.rule _ pre) (CommonTapes.config _ _ f) = _
    rw [CommonTapes.advance_config,Generator.Input.halted]; rfl
  have v₁ := CommonTapes.visits copyIndex pre old a _ _ (Generator.Input.space b mark cons one H j)
  have ca : aa.tape = old := by
    apply idle
    · intro i
      cases i with
      | false => rfl
      | true =>
        change Tape.loaded b [] = GeneratorPipeline.mapTape _ (Tape.loaded none [])
        rw [map_loaded]; rfl
    · intro _ _; rfl
  have cf : ff.tape = Sum.elim (fun _ => src) g.tape := by
    apply idle
    · intro i
      cases i with
      | false => rfl
      | true => exact (main_tape blank j d).symm
    · intro i h
      rcases i with _ | k
      · rfl
      · rcases k with k | k
        · cases k with
          | main => exact (h ⟨true,rfl⟩).elim
          | rev | aux | stack => rfl
        · cases k <;> rfl
  have cg : gg.tape = Sum.elim (fun _ => src) g.tape := pipeline_bank src _ old rfl
  have eqg : gg = ⟨g.pc,ff.tape⟩ := by exact congrArg (Config.mk g.pc) (cg.trans cf.symm)
  have ea : aa = ⟨.copy,old⟩ := congrArg (Config.mk _) ca
  change VisitsAtMost (copyRule blank mark) aa _ _ at v₁
  rw [ea] at s₁ v₁
  exact ⟨ff,s₁,h₁,v₁,eqg⟩

/-- Every finite prefix of the generator and interpreter runs after the unary adapter. -/
theorem run_prefix [Finite A] [Fintype I] (blank : A) (mark : Letter A I)
    (distinct : Sum.inl blank ≠ mark) (c : Code) (enum : Tag A I ≃ Fin (M+1))
    (H : ℤ) (j : ℕ) (d : I → Tape A)
    {z : Config (Letter A I) (GeneratorPipeline.Control c M) (GeneratorPipeline.Index I)} {t : ℕ}
    (tr : Trace (advance (GeneratorPipeline.rule blank c enum))
      (GeneratorPipeline.initial blank c (unaryInput j) d) t z) :
    Trace (advance (rule blank mark c enum)) (initial blank mark c H j d)
      (2*j+5+t) (finalCfg blank mark H j z) := by
  let old := unaryTapes blank mark H j d
  let zz := CommonTapes.config pipelineIndex old z
  obtain ⟨f,first,stop,_,eqg⟩ := copy_phase (M := M) blank mark distinct c H j d
  have second := CommonTapes.trace pipelineIndex (GeneratorPipeline.rule blank c enum) old tr
  rw [eqg] at second
  have allSteps := ((TapeSequence.first_trace _ (pipelineRule blank c enum) _ first).trans
    (.single (TapeSequence.handoff _ _ _ stop))).trans
    (TapeSequence.second_trace _ _ _ second)
  let src := Generator.Input.source (.inl blank) mark H j
  have cz : zz.tape = Sum.elim (fun _ => src) z.tape := pipeline_bank src _ old rfl
  have ez : TapeSequence.relabel (T := Control c M) Sum.inr zz =
      finalCfg blank mark H j z := congrArg (Config.mk _) cz
  rw [← ez]
  exact allSteps

/-- Any halting pipeline computation from the encoded input runs on the same
hardware from ordinary unary marks. Its time gains exactly the adapter and
one dispatch. The extra tape returns to its initial head and contents. -/
theorem run [Finite A] [Fintype I] (blank : A) (mark : Letter A I)
    (distinct : Sum.inl blank ≠ mark) (c : Code) (enum : Tag A I ≃ Fin (M+1))
    (H : ℤ) (j : ℕ) (d : I → Tape A)
    {z : Config (Letter A I) (GeneratorPipeline.Control c M) (GeneratorPipeline.Index I)} {t S : ℕ}
    (tr : Trace (advance (GeneratorPipeline.rule blank c enum))
      (GeneratorPipeline.initial blank c (unaryInput j) d) t z)
    (halt : advance (GeneratorPipeline.rule blank c enum) z = none)
    (vis : VisitsAtMost (GeneratorPipeline.rule blank c enum)
      (GeneratorPipeline.initial blank c (unaryInput j) d) t S) :
    let m := rule blank mark c enum
    let x := initial blank mark c H j d
    let y := finalCfg blank mark H j z
    Trace (advance m) x (2*j+5+t) y ∧ advance m y = none ∧
      VisitsAtMost m x (2*j+5+t) (8*j+18 + S + 2*(Fintype.card I+7)) := by
  let src := Generator.Input.source (.inl blank) mark H j
  let old := unaryTapes blank mark H j d
  let g := GeneratorPipeline.initial (M := M) blank c (unaryInput j) d
  let gg := CommonTapes.config pipelineIndex old g
  let zz := CommonTapes.config pipelineIndex old z
  let pipeline := GeneratorPipeline.rule blank c enum
  obtain ⟨ff,s₁,h₁,v₁,eqg⟩ := copy_phase (M := M) blank mark distinct c H j d
  have s₂ := CommonTapes.trace pipelineIndex pipeline old tr
  have h₂ : advance (pipelineRule blank c enum) zz = none := by
    change advance (CommonTapes.rule _ pipeline) (CommonTapes.config _ _ z) = _
    rw [CommonTapes.advance_config,halt]; rfl
  have v₂ := CommonTapes.visits pipelineIndex pipeline old g _ _ vis
  have cz : zz.tape = Sum.elim (fun _ => src) z.tape := pipeline_bank src _ old rfl
  change Trace (advance (pipelineRule blank c enum)) gg t zz at s₂
  change VisitsAtMost (pipelineRule blank c enum) gg t _ at v₂
  change gg = _ at eqg
  rw [eqg] at s₂ v₂
  obtain ⟨allSteps,stops⟩ := TapeSequence.run _ _ _ s₁ h₁ s₂ h₂
  have bound := TapeSequence.visitsAtMost _ _ _ s₁ h₁ s₂ v₁ v₂
  have ez : TapeSequence.relabel (T := Control c M) Sum.inr zz =
      finalCfg blank mark H j z := congrArg (Config.mk _) cz
  rw [ez] at allSteps
  rw [ez] at stops
  refine ⟨allSteps,stops,?_⟩
  have count : Fintype.card (Index I) = Fintype.card I + 7 := by
    have four : Fintype.card K' = 4 := by decide
    simp [Index,GeneratorPipeline.Index,Universal.Index,four,Fintype.card_sum]
    omega
  rw [count] at bound
  convert bound using 1 <;> first | rfl | omega

end
end GeneratorInputRun

end NearSquareRoot
end Computability
end OAI
