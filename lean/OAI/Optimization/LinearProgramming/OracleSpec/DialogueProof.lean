import OAI.Optimization.LinearProgramming.OracleSpec.Dialogue

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace Dialogue

variable {k : ℕ} {I : Type*} {C : Type*}

open ExactQuantumFactoring.BitStackProgram
open BitCode

/-- A complete interactive computation. The bound limits the actual encoding of each
visited state and every submitted word, including the final state. The round count includes
the final call to `dispatch` that emits an answer. -/
inductive Session (ei : I → Word) (ec : C → Word) (dispatch : I ⊕ (Bool × C) → Bool ⊕ (Word × C))
    (reply : Transcript → Word → Bool) (L : ℕ) : I ⊕ (Bool × C) → Transcript → Bool → Transcript → ℕ → Prop where
  | done {s h b} (hr : dispatch s = .inl b) (hs : (inputCode ei ec s).length ≤ L) :
      Session ei ec dispatch reply L s h b h 1
  | query {s h word carry b out n} (hr : dispatch s = .inr (word,carry))
      (hs : (inputCode ei ec s).length ≤ L) (hw : word.length ≤ L)
      (rest : Session ei ec dispatch reply L (.inr (reply h word,carry))
        ((word,[reply h word]) :: h) b out n) : Session ei ec dispatch reply L s h b out (n+1)

namespace Ports

private theorem done_body (d : Ports k) {pureStep : BitCode k} {o : WordOracle} {m h n b}
    (hr : Executes d.io o pureStep m (d.mem [false,b] [] [] [] h) n) :
    Executes d.io o (d.body pureStep) m (d.mem [] [] [] [b] h) (n+4) := by
  have dr : Executes d.io o (drain d.wire) (d.mem [b] [] [] [] h) (d.mem [] [] [] [b] h) 3 := by
    simpa [Memory.drained, mem] using drain_exec d.wire d.io o (d.mem [b] [] [] [] h)
  apply Executes.seq hr
  apply Executes.casesFalse (a := 3) (xs := [b]) (by simp [mem]); simpa using dr

private theorem query_body (d : Ports k) {pureStep : BitCode k} {reply : Transcript → Word → Bool}
    {m h n word c} (hr : Executes d.io (fun past q => [reply past q]) pureStep m
      (d.mem (true :: (frame word ++ c)) [] [] [] h) n) :
    let b := reply h word
    Executes d.io (fun past q => [reply past q]) (d.body pureStep) m
      (d.mem (true::b::c) [] [true] [] ((word,[b])::h)) (n+(1+(10*word.length+13))) := by
  apply Executes.seq hr
  apply Executes.casesTrue (xs := frame word ++ c) (by simp [mem])
  simpa using d.nextStep_exec reply word c h

/-- The upper bound derived from the *actual* finite controller and one ordinary dispatch
procedure. The numerical enclosure follows by induction on completed adaptive sessions. -/
theorem loop_exec (d : Ports k) (pureStep : BitCode k) (ei : I → Word) (ec : C → Word)
    (dispatch : I ⊕ (Bool × C) → Bool ⊕ (Word × C)) (reply : Transcript → Word → Bool) (L P : ℕ)
    (stepRuns : ∀ s h, (inputCode ei ec s).length ≤ L → ∃ n ≤ P,
      Executes d.io (fun past q => [reply past q]) pureStep (d.mem (inputCode ei ec s) [] [] [] h)
        (d.mem (actionCode ec (dispatch s)) [] [] [] h) n)
    {s h v history rounds} (hs : Session ei ec dispatch reply L s h v history rounds) :
    ∃ n ≤ rounds*(P+10*L+15), Executes d.io (fun past q => [reply past q]) (d.loopCode pureStep)
      (d.mem (inputCode ei ec s) [] [true] [] h) (d.mem [] [] [] [v] history) n := by
  induction hs with
  | @done s h b hr hlen =>
    obtain ⟨n,hn,run⟩ := stepRuns s h hlen
    rw [hr] at run
    have bodyRun := d.done_body (b := b) run
    have first : (d.mem (inputCode ei ec s) [] [true] [] h).pop d.ctrl =
        d.mem (inputCode ei ec s) [] [] [] h := by simp
    refine ⟨1 + ((n+4)+1), by simp; omega, ?_⟩
    apply Executes.loopTrue (xs := []) (by simp [mem])
    · rw [first]; exact bodyRun
    · exact Executes.loopNil (by simp [mem])
  | @query s h word carry b out r hr hlen hw _ ih =>
    obtain ⟨n,hn,run⟩ := stepRuns s h hlen
    obtain ⟨z,hz,later⟩ := ih
    rw [hr] at run
    have bodyRun := d.query_body (word := word) (c := ec carry) run
    refine ⟨1 + ((n+(1+(10*word.length+13)))+z), ?_, ?_⟩
    · rw [Nat.add_mul r 1, Nat.one_mul]; omega
    · apply Executes.loopTrue (xs := []) (by simp [mem])
      · simpa using bodyRun
      · exact later

theorem store_singleton (d : Ports k) (w : Word) :
    d.store w [] [] = singletonStore d.wire w := by
  funext i
  by_cases hi : i = d.wire <;> simp [store, singletonStore, hi]

theorem source_start (d : Ports k) (input : Word) :
    startMemory d.wire input = d.mem input [] [] [] [] := by
  simp only [startMemory, mem, store_singleton, Memory.mk.injEq, and_true]
  funext i
  by_cases hi : i = d.wire <;> simp [singletonStore, hi]

/-- The structured execution composes the unpadded dialogue with explicit input preparation. -/
theorem code_exec (d : Ports k) (pureStep : BitCode k) (ei : I → Word) (ec : C → Word)
    (dispatch : I ⊕ (Bool × C) → Bool ⊕ (Word × C)) (reply : Transcript → Word → Bool) (L P : ℕ)
    (stepRuns : ∀ s h, (inputCode ei ec s).length ≤ L → ∃ n ≤ P,
      Executes d.io (fun past q => [reply past q]) pureStep (d.mem (inputCode ei ec s) [] [] [] h)
        (d.mem (actionCode ec (dispatch s)) [] [] [] h) n)
    {x v history rounds} (hs : Session ei ec dispatch reply L (.inl x) [] v history rounds) :
    ∃ n ≤ rounds*(P+10*L+15)+2, Executes d.io (fun past q => [reply past q]) (d.code pureStep)
      (startMemory d.wire (ei x)) (d.mem [] [] [] [v] history) n := by
  obtain ⟨n,hn,loopRun⟩ := d.loop_exec pureStep ei ec dispatch reply L P stepRuns hs
  have tag := Executes.push (answer := d.io) (o := fun past w => [reply past w])
    (d.mem (ei x) [] [] [] []) d.wire false
  have flag := Executes.push (answer := d.io) (o := fun past w => [reply past w])
    (d.mem (false::ei x) [] [] [] []) d.ctrl true
  simp only [push_wire] at tag
  simp only [push_ctrl] at flag
  refine ⟨1+(1+n), by omega, ?_⟩
  rw [d.source_start]
  exact Executes.seq tag (Executes.seq flag loopRun)

/-- Add the public-input tag and loop marker, then run the checked controller and issue
the final `halt`. The bound holds for an arbitrary adaptive oracle. -/
theorem computes (d : Ports k) (pureStep : BitCode k) (ei : I → Word) (ec : C → Word)
    (dispatch : I ⊕ (Bool × C) → Bool ⊕ (Word × C)) (reply : Transcript → Word → Bool) (L P : ℕ)
    (stepRuns : ∀ s h, (inputCode ei ec s).length ≤ L → ∃ n ≤ P,
      Executes d.io (fun past q => [reply past q]) pureStep (d.mem (inputCode ei ec s) [] [] [] h)
        (d.mem (actionCode ec (dispatch s)) [] [] [] h) n)
    {x v history rounds} (hs : Session ei ec dispatch reply L (.inl x) [] v history rounds) :
    ((d.code pureStep).compile d.wire d.io).ComputesWithin (fun past q => [reply past q]) (ei x)
      (rounds*(P+10*L+15)+3) (fun hist out => hist = history ∧ out = [v]) := by
  obtain ⟨n, hn, run⟩ := d.code_exec pureStep ei ec dispatch reply L P stepRuns hs
  apply compile_computes run (by omega)
  exact ⟨rfl, rfl⟩

end Ports
end Dialogue
end OracleSpec
end LinearProgramming
end Optimization
end OAI
