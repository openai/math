import OAI.Computability.BorderVNP.TeamBurstProbeStepWords
import OAI.Computability.BorderVNP.TeamProbeEmit
import OAI.Computability.BorderVNP.TeamWordAssignments

/-! # One physical probe in a team's consecutive burst read

A guessed word is both the previous and resulting value of a read-only probe. The
machine emits its two physical records, accumulates its bits for the private verifier
and advances the shared address and tick before starting the next guess.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamBurstProbeStep

open VPVNP RAMTape BurstRAM RAMSerialization TeamProbeEmit

variable {w H : ℕ}

/-- The emitter's registers, the reversed private string, and the caller's loop ports. -/
inductive Port where
  | probe (p : TeamProbeEmit.Port)
  | privateReverse | privateInput | marks | width | saved
  deriving DecidableEq, Fintype

/-- A logical operand in the shared probe emitter. -/
abbrev word (i : Operand) : Port := .probe (.operand i)

private def operands (a tick old : Word w) : Operand → Word w
  | .address => a
  | .tick => tick
  | .before | .after => old

/-- The two widened sorting slots for a read-only burst probe. -/
def pair (a tick old : Word w) : List (WordRecord (w+1)) :=
  let z := operands a tick old
  TeamTapeSorting.wordPair (widenRecord (TeamProbeEmit.probe z)) (probeFits z)

/-- At a burst-word boundary the next guess starts on a blank previous-word stack. -/
structure Ready (hw : 2 ≤ w+1) (H : ℕ) (a tick : Word w)
    (rs : List (WordRecord (w+1))) (rev : List Bool) (s : Stacks Port) : Prop where
  /-- Address of the next consecutive word. -/
  address : s (word .address) = BurstRAM.wordBits a
  /-- Logical time of this probe. -/
  time : s (word .tick) = BurstRAM.wordBits tick
  /-- Destination for the next word guess. -/
  before : s (word .before) = []
  /-- The read-only probe's result word will be staged here. -/
  after : s (word .after) = []
  /-- Words read so far, accumulated in reverse bit order. -/
  bytes : s .privateReverse = rev
  /-- Empty temporary stack for copying and incrementing words. -/
  scratch : s (.probe .temp) = []
  /-- Reusable widened registers contain at most one widened word. -/
  lifted : ∀ k, (s (.probe (.lifted k))).length ≤ w+1
  /-- The physical sorter already contains precisely the specified prefix. -/
  buffer : RecordBuffer.Holds hw H rs (s ∘ Port.probe ∘ TeamProbeEmit.Port.buffer)
  /-- Reusable serialization registers fit the sorting width. -/
  fields : ∀ j, (s (.probe (.buffer (.field j)))).length ≤ w+1

private abbrev tmp : Port := .probe .temp

private def finish : FiniteRoutine Port :=
  ((EvaluatorRadixDivision.reverseOnto (word .before) .privateReverse).followedBy
    (SliceArithmetic.CallClear.clear (word .after))).followedBy
    ((increment (word .address) tmp).followedBy (increment (word .tick) tmp))

/-- The deterministic portion of one burst iteration, immediately after the word guess. -/
def program : FiniteRoutine Port :=
  ((TeamWords.assign (word .before) (word .after) tmp).followedBy
    (TeamProbeEmit.program.onPorts Port.probe)).followedBy finish

/-- The post-guess machine emits exactly the read and write halves, collects the old
word in reverse, clears both guess operands, advances both counters modulo the word
range, and preserves the four caller stacks. -/
theorem runs {hw : 2 ≤ w+1} {a tick : Word w} {rs : List (WordRecord (w+1))}
    {rev : List Bool} {s : Stacks Port} (ready : Ready hw H a tick rs rev s)
    (old : Word w) (free : rs.length+2 ≤ 4*H) :
    ∃ n out, n ≤ 200*w+230 ∧ program.Runs n (Function.update s (word .before) (BurstRAM.wordBits old)) out ∧
      Ready hw H (next a) (next tick) (rs++pair a tick old) ((BurstRAM.wordBits old).reverse++rev) out ∧
      out .marks = s .marks ∧ out .width = s .width ∧ out .saved = s .saved ∧
      out .privateInput = s .privateInput := by
  let g := Function.update s (word .before) (BurstRAM.wordBits old)
  let u := Function.update g (word .after) (BurstRAM.wordBits old)
  have hg : g (word .before) = BurstRAM.wordBits old := Function.update_self ..
  have copy := TeamWords.assign_runs (word .before) (word .after) tmp (by decide) (by decide)
    (by decide) g ready.scratch
  rw [hg, length_wordBits, show g (word .after) = [] from ready.after] at copy
  have staged : Staged hw H (operands a tick old) rs (u ∘ Port.probe) := by
    refine ⟨?_,ready.scratch,ready.lifted,ready.buffer,ready.fields⟩
    intro i
    cases i with
    | address => exact ready.address
    | tick => exact ready.time
    | before => exact hg
    | after => exact Function.update_self (word .after) (BurstRAM.wordBits old) g
  obtain ⟨n,emitted,hn,emitRun,endStage⟩ := TeamProbeEmit.runs staged free
  let v := installStacks Port.probe u emitted
  have inj : Function.Injective Port.probe := fun _ _ he => Port.probe.inj he
  have inside : v ∘ Port.probe = emitted := funext (installStacks_at inj u emitted)
  have outside {p : Port} (hp : ∀ i, Port.probe i ≠ p) : v p = u p :=
    installStacks_outside u emitted hp
  have emit := TeamProbeEmit.program.runs_onPorts inj u emitRun
  rw [installStacks_eq inj u (u ∘ Port.probe) (fun _ => rfl)] at emit
  rw [← inside] at endStage
  have oldV : v (word .before) = BurstRAM.wordBits old := endStage.operands .before
  have afterV : v (word .after) = BurstRAM.wordBits old := endStage.operands .after
  have revV : v .privateReverse = rev := (outside (by simp)).trans ready.bytes
  let r := Function.update (Function.update v (word .before) []) .privateReverse ((BurstRAM.wordBits old).reverse++rev)
  have collect := EvaluatorRadixDivision.reverseOnto_runs (src := word .before) (dst := .privateReverse)
    (by decide) v r rfl (by simp [r, oldV, revV]) (fun k hk hd => by simp [r, hk, hd])
  rw [oldV, length_wordBits] at collect
  let cleared := Function.update r (word .after) []
  have clear := SliceArithmetic.CallClear.clear_runs (word .after) r
  rw [show r (word .after) = BurstRAM.wordBits old from afterV, length_wordBits] at clear
  let bumped := Function.update cleared (word .address) (BurstRAM.wordBits (next a))
  let out := Function.update bumped (word .tick) (BurstRAM.wordBits (next tick))
  have ha := increment_runs (word .address) tmp (by decide) cleared a
    (endStage.operands .address) endStage.scratch
  have ht := increment_runs (word .tick) tmp (by decide) bumped tick
    (endStage.operands .tick) endStage.scratch
  refine ⟨_, out, ?_, (copy.followedBy emit).followedBy ((collect.followedBy clear).followedBy
    (ha.followedBy ht)), ?_, outside (by simp), outside (by simp), outside (by simp), outside (by simp)⟩
  · simp only [List.length_nil]; omega
  · exact ⟨by simp [out, bumped, word], by simp [out], by simp [out, bumped, cleared, r, word],
      by simp [out, bumped, cleared, word], by simp [out, bumped, cleared, r, word],
      endStage.scratch, endStage.work, endStage.buffer, endStage.fields⟩

end TeamBurstProbeStep

end BorderVNP
end Computability
end OAI
