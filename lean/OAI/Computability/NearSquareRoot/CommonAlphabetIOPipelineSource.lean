import OAI.Computability.NearSquareRoot.CommonAlphabetIOPipelineROM
import OAI.Computability.NearSquareRoot.CommonAlphabetPublicAligned

/-! # Compiling a variable-alphabet source with literal binary I/O

The program table depends on the finite source machine and its enumerations.
The two literal input words and the result are run data. One auxiliary head
repositions the designated output before the two-tape compactor reads it.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Pipeline
open IntegerMultiplication TM
open Public (Letter)

variable {A I Q : Type} [DecidableEq I]

/-- The source machine receives its unexpanded input on its designated tape. -/
def sourceLoad (srcBit : Bool → A) (srcSep : A) (inp : I) (x y : List Bool) : I → List A :=
  load inp [] (srcWord srcBit srcSep x y)

private theorem input_eq {R : Type} (pc : R) (c : Code A) (srcBit : Bool → A)
    (srcSep : A) (inp : I) (x y : List Bool) :
    loadedConfig pc (none : Letter)
      (fun j : Option I => match j with
        | none => []
        | some i => (c.encodeList (sourceLoad srcBit srcSep inp x y i)).map Public.emb) =
      ⟨pc,coreLoad c srcBit srcSep (some inp) x y⟩ := by
  apply congrArg (Config.mk pc)
  funext i
  cases i with
  | none => simp [coreLoad,load,Function.update]
  | some i =>
    by_cases e : i = inp <;> simp [sourceLoad,coreLoad,load,Function.update,e]

abbrev SourceControl (A Q I : Type) (w : ℕ) := Control A (Align.Phase (PC A Q I w)) w

def sourceEntry (A Q I : Type) (w : ℕ) : SourceControl A Q I w :=
  entry A (Align.Phase (PC A Q I w)) w

/-- The compiled candidate on the common public alphabet before interpretation. -/
def sourceMachine (c : Code A) (srcBit : Bool → A) (srcSep : A) (decode : A → Option Bool)
    (inp out : I) (m : Rule A Q I) (q : Q) : Rule Letter (SourceControl A Q I c.width) (Index (Option I)) :=
  machine c srcBit srcSep decode (some inp) (some out) (Public.alignedRule c m out q) .boot

/-- Run the raw four-letter candidate directly. A scheduler may fence, clock or
compose this physical machine before constructing its common transition ROM. -/
theorem literal_from_source [Fintype I] (c : Code A) (srcBit : Bool → A) (srcSep srcBlank : A)
    (hb : c.enc srcBlank = fun _ => none) (decode : A → Option Bool)
    (empty : decode srcBlank = none) (digits : ∀ b, decode (srcBit b) = some b)
    (inp out : I) (m : Rule A Q I) (q : Q) (x y z : List Bool)
    {n cells : ℕ} (finish : Config A Q I)
    (hist : Trace (advance m) (loadedConfig q srcBlank (sourceLoad srcBit srcSep inp x y)) n finish)
    (halt : advance m finish = none) (result : whole srcBlank (z.map srcBit) (finish.tape out))
    (space : VisitsAtMost m (loadedConfig q srcBlank (sourceLoad srcBit srcSep inp x y)) n cells) :
    let candidate := sourceMachine c srcBit srcSep decode inp out m q
    let init := (⟨sourceEntry A Q I c.width,publicLoad x y⟩ : Config Letter _ (Index (Option I)))
    let e := expandSteps c.width x y
    let d := compactSteps c.width z
    let H := Fintype.card (Index (Option I))
    let coreSpace := 2*((2*(1+5*c.width)+1)*cells)
    ∃ ticks stop, ticks ≤ e+1+(2*clock c n+3)+1+d ∧ Trace (advance candidate) init ticks stop ∧
      advance candidate stop = none ∧ stop.tape (.inl true) = Tape.loaded none (z.map Public.bit) ∧
      VisitsAtMost candidate init ticks (2*(e+1)+H+(coreSpace+H)+(2*(d+1)+H)) := by
  obtain ⟨t,w,ht,run,done,word,cells'⟩ := Public.executeAligned c m q srcBlank hb
    (sourceLoad srcBit srcSep inp x y) n cells finish out (z.map srcBit) hist halt result space
  let start : Config Letter (Align.Phase (PC A Q I c.width)) (Option I) :=
    ⟨.boot,coreLoad c srcBit srcSep (some inp) x y⟩
  have hstart := input_eq (Align.Phase.boot : Align.Phase (PC A Q I c.width)) c srcBit srcSep inp x y
  have actual : Trace (advance (Public.alignedRule c m out q)) start t w := by
    dsimp only [start]
    rw [← hstart]
    exact run
  have cover' : VisitsAtMost (Public.alignedRule c m out q) start t
      (2*((2*(1+5*c.width)+1)*cells)) := by
    dsimp only [start]
    rw [← hstart]
    exact cells'
  obtain ⟨trace,stopped,cover⟩ := Pipeline.run c srcBit srcSep srcBlank hb decode empty digits
    (some inp) (some out) (Public.alignedRule c m out q) .boot x y z w actual done word cover'
  exact ⟨_,_,by omega,trace,stopped,rfl,cover⟩

/-- A finite source transition function and explicit finite numberings give
the entire four-letter ROM, including expansion, alignment and compaction. -/
def sourceProgram (a : Numbering A) (control : Numbering Q) (index : Numbering I)
    (c : Code A) (srcBit : Bool → A) (srcSep : A) (decode : A → Option Bool)
    (inp out : I) (m : Rule A Q I) (q : Q) :=
  program a (Numbering.controller a control index c.width).align index.option
    c srcBit srcSep decode (some inp) (some out) (Public.alignedRule c m out q) .boot

/-- The fixed interpreter executes the complete compiled program from the raw
public words and its installed ROM. Its final designated literal tape starts
at zero, includes every leading zero bit and is otherwise blank. -/
theorem installed_from_source [Fintype I] (a : Numbering A) (control : Numbering Q)
    (index : Numbering I) (c : Code A) (srcBit : Bool → A) (srcSep srcBlank : A)
    (hb : c.enc srcBlank = fun _ => none) (decode : A → Option Bool)
    (empty : decode srcBlank = none) (digits : ∀ b, decode (srcBit b) = some b)
    (inp out : I) (m : Rule A Q I) (q : Q) (x y z : List Bool)
    {n cells : ℕ} (finish : Config A Q I)
    (hist : Trace (advance m) (loadedConfig q srcBlank (sourceLoad srcBit srcSep inp x y)) n finish)
    (halt : advance m finish = none) (result : whole srcBlank (z.map srcBit) (finish.tape out))
    (space : VisitsAtMost m (loadedConfig q srcBlank (sourceLoad srcBit srcSep inp x y)) n cells) :
    let rom := sourceProgram a control index c srcBit srcSep decode inp out m q
    let K := 4*(rom.length+1)
    let H := Fintype.card (Index (Option I))
    let e := expandSteps c.width x y
    let d := compactSteps c.width z
    let coreSpace := 2*((2*(1+5*c.width)+1)*cells)
    let init := TapeSequence.relabel Sum.inl (Universal.Loader.initial none rom (publicLoad x y))
    let interpreter := Universal.Loader.installAndRun (I := Index (Option I)) (none : Letter)
    ∃ ticks stop, ticks ≤ 2*rom.length+3+K*(e+1+(2*clock c n+3)+1+d+1) ∧
      Trace (advance interpreter) init ticks stop ∧ advance interpreter stop = none ∧
      stop.tape (.inl (.inl true)) =
        Tape.loaded (.inl none) (z.map (fun b => .inl (Public.bit b))) ∧
      VisitsAtMost interpreter init ticks
        (H+2*(rom.length+1)+((2*(e+1)+H+(coreSpace+H)+(2*(d+1)+H))*(2*K+1)+2*(rom.length+2*K+1))) := by
  obtain ⟨t,w,ht,run,done,word,cover⟩ := literal_from_source c srcBit srcSep srcBlank hb decode
    empty digits inp out m q x y z finish hist halt result space
  let nums := (Numbering.publicIndex index.option).arrow Numbering.publicLetter
  let states := Numbering.pipeline a (Numbering.controller a control index c.width).align c.width
  obtain ⟨ticks,stop,bound,physical,stopped,correct,visits⟩ := Universal.Reindex.install_numbered
    states.equiv (sourceEntry A Q I c.width) none (sourceMachine c srcBit srcSep decode inp out m q)
    nums.all nums.mem_all (publicLoad x y) run done cover
  refine ⟨ticks,stop,bound.trans ?_,physical,stopped,?_,visits⟩
  · apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    omega
  · rw [correct,word]
    exact literal_data z

end CommonAlphabet.Pipeline

end NearSquareRoot
end Computability
end OAI
