import OAI.Computability.BorderVNP.TeamBurstProbeControl

/-! # Path replay through the consecutive team-memory probe loop

For every list of old words the enclosing physical interpreter consumes exactly the bit
choices encoding that list, appends the consecutive timed read pairs, and releases the
ordered private input. All choice bits belonging to later calls are preserved.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamBurstProbe

open VPVNP RAMTape BurstRAM TeamPrivateFragment
open TeamBurstProbeStep (Port Ready next pair word)

/-- The order of choices along the physical word-guesser path. -/
def choices {w : ℕ} (vs : List (Word w)) : List Bool :=
  vs.flatMap (fun v => (wordBits v).reverse)

/-- Uniform upper bound on one burst, including the final reversal of all collected bits. -/
def loopTime (w q previousBits : ℕ) : ℕ :=
  q*(206*w+233)+2*(previousBits+q*w)+2

private theorem loopTime_succ (w q k : ℕ) :
    loopTime w (q+1) k = 1+(6*w+2)+(200*w+230)+loopTime w q (w+k) := by
  unfold loopTime
  ring

/-- Replay each guess along the actual word-choice rows, emit its two physical records,
and deliver the chronological word bytes to the enclosing signed private call. -/
theorem replay_runs {K R : Type} [DecidableEq K] (target : StackCode K R)
    (ports : Port → K) (hp : Function.Injective ports) (label : LoopState → R)
    (resume : R) (hr : ∀ j, target (label j) = rows ports label resume j)
    (base : Stacks K) {w H : ℕ} {hw : 2 ≤ w+1} (vs : List (Word w))
    (a tick : Word w) (rs : List (RAMSerialization.WordRecord (w+1))) (rev suffix : List Bool)
    (s : Stacks Port) (ready : LoopReady hw H a tick rs rev vs.length s)
    (free : rs.length+2*vs.length ≤ 4*H) :
    ∃ t u, t ≤ loopTime w vs.length rev.length ∧
      StackRuns (replay target) t (label .test, choices vs++suffix) (installStacks ports base s)
        (resume,suffix) (installStacks ports base u) ∧
      Ready hw H (advance vs.length a) (advance vs.length tick) (rs++records a tick vs) [] u ∧
      u .privateInput = rev.reverse++bytes vs ∧ u .marks = [] ∧
      u .width = List.replicate w true ∧ u .saved = [] := by
  induction vs generalizing a tick rs rev s with
  | nil =>
    have first := emptyMark target ports hp label resume hr base ready
    have last := finishRun target ports hp label resume hr base s rev ready.step.bytes ready.input
    have run := replay_segment (first.trans last) suffix
    refine ⟨_,finalized s rev, ?_, run, ?_, ?_, ready.marks, ready.width, ready.saved⟩
    · simp [loopTime]; omega
    · simpa only [records,List.append_nil,List.length_nil,advance,Nat.rec_zero] using finalized_ready ready
    · simp [finalized,bytes]
  | cons v vs ih =>
    have pop := consumeMark target ports hp label resume hr base ready
    have marked := ready.pop
    let u := afterPop s vs.length
    have guess := TeamGuessWord.replay_runs target (ports ∘ guessPorts)
      (hp.comp guessPorts_injective) (guessLabel label) (installStacks ports base u)
      (guessRows target ports label resume hr) (List.replicate w true) (wordBits v)
      (choices vs++suffix) (by simp [length_wordBits])
    rw [guessInput ports hp base marked, guessOutput ports hp base marked] at guess
    simp only [List.length_replicate] at guess
    have freeStep : rs.length+2 ≤ 4*H := by simp only [List.length_cons,Nat.mul_add] at free; omega
    obtain ⟨n,s',hn,emit,nextReady⟩ := afterGuess target ports hp label resume hr base marked v freeStep
    have freeNext : (rs++pair a tick v).length+2*vs.length ≤ 4*H := by
      rw [List.length_append, show (pair a tick v).length = 2 from rfl]
      simp only [List.length_cons,Nat.mul_add] at free
      omega
    obtain ⟨n',out,hn',later,recordsReady,input,marks,width,saved⟩ :=
      ih (next a) (next tick) (rs++pair a tick v) ((wordBits v).reverse++rev) s' nextReady freeNext
    have run := (((replay_segment pop ((wordBits v).reverse++(choices vs++suffix))).trans guess).trans
      (replay_segment emit (choices vs++suffix))).trans later
    refine ⟨1+(6*w+2)+n+n',out,?_,?_,?_,?_,marks,width,saved⟩
    · rw [List.length_cons,loopTime_succ]
      simp only [List.length_append,List.length_reverse,length_wordBits] at hn'
      omega
    · simpa only [choices,List.flatMap_cons,List.append_assoc] using run
    · simpa only [List.length_cons,advance_succ,records,List.append_assoc] using recordsReady
    · simpa only [List.reverse_append,List.reverse_reverse,List.append_assoc,bytes,List.flatMap_cons] using input

end TeamBurstProbe

end BorderVNP
end Computability
end OAI
