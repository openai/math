import OAI.Computability.BorderVNP.TeamBurstProbeStep
import OAI.Computability.BorderVNP.TeamGuessReplay
import OAI.Computability.BorderVNP.TeamPrivateCall
import OAI.Computability.VPVNP.EvaluatorRadixDivision

/-! # Fixed control for the consecutive shared-memory reads of a private call

Each consumed length mark leads through one genuine width-bit guess and one timed pair
emission. The final empty pop restores the private input to forward byte order. The rows
are parameterized by physical port and control-label embeddings so the private call and
its signed continuation can be linked without introducing another nondeterministic step.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamBurstProbe

open VPVNP RAMTape BurstRAM
open TeamBurstProbeStep (Port Ready next pair word)

/-- Emit the accumulated words in chronological order on the private input stack. -/
def finish : FiniteRoutine Port := EvaluatorRadixDivision.reverseOnto .privateReverse .privateInput

/-- Fixed states of the variable-length probe loop. -/
inductive LoopState
  | test
  | guess (q : TeamGuessWord.State)
  | emit (q : TeamBurstProbeStep.program.State)
  | finish (q : finish.State)
  deriving Fintype

noncomputable instance : DecidableEq LoopState := Classical.decEq _

/-- The guessing routine writes directly to the read's previous-word register. -/
def guessPorts : TeamGuessWord.Port → Port
  | .width => .width
  | .saved => .saved
  | .out => word .before

theorem guessPorts_injective : Function.Injective guessPorts := by decide

/-- The terminal guess state is the entry to the physical deterministic emission. -/
def guessLabel {R : Type*} (label : LoopState → R) : TeamGuessWord.State → R
  | .done => label (.emit TeamBurstProbeStep.program.body.entry)
  | q => label (.guess q)

/-- Embed the entire loop directly into the outer validator. The empty counter goes to
the private-input reversal; the two choices in each old-word bit remain distinct. -/
def rows {K R : Type} (ports : Port → K) (label : LoopState → R) (resume : R) :
    LoopState → StackOp K R
  | .test => .pop (ports .marks) fun b => b.elim (label (.finish finish.body.entry))
      (fun _ => guessLabel label .scan)
  | .guess q => (TeamGuessWord.code q).rename (ports ∘ guessPorts) (guessLabel label)
  | .emit q => (TeamBurstProbeStep.program.body.code q).rename ports (Option.elim · (label .test) (label ∘ LoopState.emit))
  | .finish q => (finish.body.code q).rename ports (Option.elim · resume (label ∘ LoopState.finish))

variable {K R : Type}

/-- Correct links from the guesser's nonterminal states. -/
theorem guessRows (target : StackCode K R) (ports : Port → K) (label : LoopState → R)
    (resume : R) (hr : ∀ q, target (label q) = rows ports label resume q)
    (q : TeamGuessWord.State) (hq : q ≠ .done) :
    target (guessLabel label q) = (TeamGuessWord.code q).rename (ports ∘ guessPorts) (guessLabel label) := by
  cases q <;> first | exact (hq rfl).elim | exact hr _

variable [DecidableEq K]

private theorem linkedRun (r : FiniteRoutine Port) (target : StackCode K R)
    (ports : Port → K) (hp : Function.Injective ports) (label : r.State → R) (resume : R)
    (hr : ∀ q, target (label q) = (r.body.code q).rename ports (Option.elim · resume label))
    (base : Stacks K) {t : ℕ} {s u : Stacks Port} (run : r.Runs t s u) :
    StackRuns target t (label r.body.entry) (installStacks ports base s) resume (installStacks ports base u) := by
  apply run.lift ports hp (fun q => q.elim resume label) base
  rintro (_ | q) hn
  · contradiction
  · exact hr q

/-- Embedded deterministic emission returns to the next counter test. -/
theorem emitRun (target : StackCode K R) (ports : Port → K) (hp : Function.Injective ports)
    (label : LoopState → R) (resume : R) (hr : ∀ q, target (label q) = rows ports label resume q)
    (base : Stacks K) {t : ℕ} {s u : Stacks Port} (run : TeamBurstProbeStep.program.Runs t s u) :
    StackRuns target t (label (.emit TeamBurstProbeStep.program.body.entry)) (installStacks ports base s)
      (label .test) (installStacks ports base u) :=
  linkedRun TeamBurstProbeStep.program target ports hp (label ∘ LoopState.emit) (label .test)
    (fun q => hr (.emit q)) base run

/-- Stack updates when a complete private argument is installed. -/
def finalized (s : Stacks Port) (rev : List Bool) : Stacks Port :=
  Function.update (Function.update s .privateReverse []) .privateInput rev.reverse

/-- Embedded chronological byte reversal delivers the private input and clears the temporary
reverse stack, including on a zero-length burst. -/
theorem finishRun (target : StackCode K R) (ports : Port → K) (hp : Function.Injective ports)
    (label : LoopState → R) (resume : R) (hr : ∀ q, target (label q) = rows ports label resume q)
    (base : Stacks K) (s : Stacks Port) (rev : List Bool)
    (hrev : s .privateReverse = rev) (hempty : s .privateInput = []) :
    StackRuns target (2*rev.length+1) (label (.finish finish.body.entry)) (installStacks ports base s)
      resume (installStacks ports base (finalized s rev)) := by
  apply linkedRun finish target ports hp (label ∘ LoopState.finish) resume (fun q => hr (.finish q)) base
  have h := EvaluatorRadixDivision.reverseOnto_runs (src := Port.privateReverse) (dst := .privateInput)
    (by decide) s (finalized s rev) (by simp [finalized]) (by simp [finalized, hrev, hempty])
    (fun k h₁ h₂ => by simp [finalized, h₁, h₂])
  simpa only [finish, hrev] using h

/-- Probe pairs emitted on a fixed chronological list of old-word choices. -/
def records {w : ℕ} (a tick : Word w) : List (Word w) → List (RAMSerialization.WordRecord (w+1))
  | [] => []
  | old :: xs => pair a tick old ++ records (next a) (next tick) xs

/-- Private byte stream in low-bit-first word order. -/
def bytes {w : ℕ} (vs : List (Word w)) : List Bool := vs.flatMap BurstRAM.wordBits

/-- Iterated modulo-word address or time counter. -/
def advance {w : ℕ} (k : ℕ) (a : Word w) : Word w :=
  Nat.rec a (fun _ b => next b) k

theorem advance_succ {w : ℕ} (k : ℕ) (a : Word w) : advance (k+1) a = advance k (next a) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg next ih

/-- A loop-ready bank, with an empty private input until the final reversal. -/
structure LoopReady {w : ℕ} (hw : 2 ≤ w+1) (H : ℕ) (a tick : Word w)
    (rs : List (RAMSerialization.WordRecord (w+1))) (rev : List Bool) (q : ℕ) (s : Stacks Port) : Prop where
  step : Ready hw H a tick rs rev s
  marks : s .marks = List.replicate q true
  width : s .width = List.replicate w true
  saved : s .saved = []
  input : s .privateInput = []

variable {w H q : ℕ} {hw : 2 ≤ w+1} {a tick : Word w}
    {rs : List (RAMSerialization.WordRecord (w+1))} {rev : List Bool} {s : Stacks Port}

/-- The deterministic removal of a length mark leaves the entire probe bank intact. -/
def afterPop (s : Stacks Port) (q : ℕ) : Stacks Port := Function.update s .marks (List.replicate q true)

omit [DecidableEq K] in
theorem LoopReady.pop (r : LoopReady hw H a tick rs rev (q+1) s) :
    LoopReady hw H a tick rs rev q (afterPop s q) :=
  ⟨⟨r.step.address,r.step.time,r.step.before,r.step.after,r.step.bytes,r.step.scratch,r.step.lifted,
      r.step.buffer,r.step.fields⟩, Function.update_self .., r.width, r.saved, r.input⟩

/-- The counter test consumes exactly one physical symbol and enters the word guess. -/
theorem consumeMark (target : StackCode K R) (ports : Port → K) (hp : Function.Injective ports)
    (label : LoopState → R) (resume : R) (hr : ∀ q, target (label q) = rows ports label resume q)
    (base : Stacks K) (r : LoopReady hw H a tick rs rev (q+1) s) :
    StackRuns target 1 (label .test) (installStacks ports base s)
      (guessLabel label .scan) (installStacks ports base (afterPop s q)) := by
  have h := StackStep.pop (s := installStacks ports base s) (k := ports .marks) (hr .test)
  simp only [installStacks_at hp, r.marks, List.replicate_succ, List.head?_cons,
    List.tail_cons, Option.elim_some, installStacks_update hp] at h
  exact .cons h (.nil ..)

/-- The empty counter enters the final reversal without modifying any stack. -/
theorem emptyMark (target : StackCode K R) (ports : Port → K) (hp : Function.Injective ports)
    (label : LoopState → R) (resume : R) (hr : ∀ q, target (label q) = rows ports label resume q)
    (base : Stacks K) (r : LoopReady hw H a tick rs rev 0 s) :
    StackRuns target 1 (label .test) (installStacks ports base s)
      (label (.finish finish.body.entry)) (installStacks ports base s) := by
  have h := StackStep.pop (s := installStacks ports base s) (k := ports .marks) (hr .test)
  simp only [installStacks_at hp, r.marks, List.replicate_zero, List.head?_nil,
    List.tail_nil, Option.elim_none, installStacks_update hp] at h
  have he : s .marks = [] := r.marks
  rw [← he, Function.update_eq_self] at h
  exact .cons h (.nil ..)

omit [DecidableEq K] in
/-- The embedded word guess begins in the supplied width template and empty old-word stack. -/
theorem guessInput (ports : Port → K) (hp : Function.Injective ports) (base : Stacks K)
    (r : LoopReady hw H a tick rs rev q s) :
    installStacks (ports ∘ guessPorts) (installStacks ports base s)
      (TeamGuessWord.bank (List.replicate w true) [] []) = installStacks ports base s := by
  apply installStacks_eq (hp.comp guessPorts_injective)
  intro j
  cases j <;> simp [installStacks_at hp, guessPorts, TeamGuessWord.bank,
    r.width, r.saved, r.step.before]

/-- Each word guess changes only the old-word operand of the ambient bank. -/
theorem guessOutput (ports : Port → K) (hp : Function.Injective ports) (base : Stacks K)
    (r : LoopReady hw H a tick rs rev q s) (bits : List Bool) :
    installStacks (ports ∘ guessPorts) (installStacks ports base s)
      (TeamGuessWord.bank (List.replicate w true) [] bits) =
    installStacks ports base (Function.update s (word .before) bits) := by
  have e : Function.update (TeamGuessWord.bank (List.replicate w true) [] []) .out bits =
      TeamGuessWord.bank (List.replicate w true) [] bits := by funext j; cases j <;> rfl
  rw [← e, ← installStacks_update (hp.comp guessPorts_injective), guessInput ports hp base r,
    ← installStacks_update hp]
  rfl

/-- Deterministically emit the just-guessed word and prepare the next iteration. -/
theorem afterGuess (target : StackCode K R) (ports : Port → K) (hp : Function.Injective ports)
    (label : LoopState → R) (resume : R) (hr : ∀ q, target (label q) = rows ports label resume q)
    (base : Stacks K) (r : LoopReady hw H a tick rs rev q s) (old : Word w) (free : rs.length+2 ≤ 4*H) :
    ∃ n u, n ≤ 200*w+230 ∧
      StackRuns target n (guessLabel label .done) (installStacks ports base (Function.update s (word .before) (wordBits old)))
        (label .test) (installStacks ports base u) ∧
      LoopReady hw H (next a) (next tick) (rs++pair a tick old) ((wordBits old).reverse++rev) q u := by
  obtain ⟨n,u,hn,run,step,hm,hwidth,hs,hi⟩ := TeamBurstProbeStep.runs r.step old free
  exact ⟨n,u,hn,emitRun target ports hp label resume hr base run,
    step, hm.trans r.marks, hwidth.trans r.width, hs.trans r.saved, hi.trans r.input⟩

/-- The final reversal clears its scratch space and preserves the complete probe prefix. -/
theorem finalized_ready (r : LoopReady hw H a tick rs rev 0 s) :
    Ready hw H a tick rs [] (finalized s rev) :=
  ⟨r.step.address,r.step.time,r.step.before,r.step.after,rfl,r.step.scratch,r.step.lifted,
    r.step.buffer,r.step.fields⟩

end TeamBurstProbe

end BorderVNP
end Computability
end OAI
