import OAI.Optimization.LinearProgramming.OracleSpec.DialogueProof

/-! An adaptive finite bit-machine driver for arbitrary reply words and arbitrary final
output words. Query, reply and output lengths all appear in the execution bound. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace WordDialogue

variable {k : ℕ} {I : Type*} {C : Type*}

open ExactQuantumFactoring.BitStackProgram BitCode
open Dialogue (Ports)

def stateCode (ei : I → Word) (ec : C → Word) : I ⊕ (Word × C) → Word
  | .inl i => false :: ei i
  | .inr (reply,carry) => true :: (frame reply ++ ec carry)

def actionCode (ec : C → Word) : Word ⊕ (Word × C) → Word
  | .inl out => false :: out
  | .inr (packet,carry) => true :: (frame packet ++ ec carry)

/-- Unframe a request and retain the continuation, issue the request, and physically frame
and prepend the complete reply to the same continuation before the next pure dispatch. -/
def askWord (d : Ports k) : BitCode k :=
  .seq (ofBitStack (unquoteMove d.wire d.io d.tmp d.ctrl))
    (.seq (queryFromStack d.io) (.seq (ofBitStack (quoteMove d.io d.wire d.tmp))
      (.seq (.push d.wire true) (.push d.ctrl true))))

theorem askWord_exec (d : Ports k) (o : WordOracle) (packet carry : Word) (h : Transcript) :
    let answer := o h packet
    Executes d.io o (askWord d) (d.mem (frame packet ++ carry) [] [] [] h)
      (d.mem (true :: (frame answer ++ carry)) [] [true] [] ((packet,answer)::h))
      (10*packet.length+8*answer.length+15) := by
  let answer := o h packet
  let h' := (packet,answer)::h
  have split := unquoteMove_runs d.wire d.io d.tmp d.ctrl (by simp [Ports.wire,Ports.io])
    (by simp [Ports.wire,Ports.tmp]) (by simp [Ports.wire,Ports.ctrl]) (by simp [Ports.io,Ports.tmp])
    (by simp [Ports.io,Ports.ctrl]) (by simp [Ports.tmp,Ports.ctrl]) packet carry
      (d.store (frame packet ++ carry) [] []) (by simp [quoteBits_eq_frame]) (by simp) (by simp)
  have u := ofBitStack_exec split d.io o [] h
  simp only [Ports.read_io,List.append_nil,Ports.write_wire,Ports.write_io] at u
  have send : Executes d.io o (queryFromStack d.io) (d.mem carry packet [] [] h)
      (d.mem carry answer [] [] h') (3*packet.length+2+answer.length) := by
    simpa [Ports.mem,Memory.drained,Memory.receive,h',answer] using
      queryFromStack_exec d.io d.io o (d.mem carry packet [] [] h) rfl
  have prepend := quoteMove_runs d.io d.wire d.tmp (by simp [Ports.io,Ports.wire])
    (by simp [Ports.io,Ports.tmp]) (by simp [Ports.wire,Ports.tmp]) (d.store carry answer []) (by simp)
  have b := ofBitStack_exec prepend d.io o [] h'
  simp only [Ports.read_io,Ports.read_wire,Ports.write_io,Ports.write_wire,quoteBits_eq_frame] at b
  have pw := Executes.push (answer := d.io) (o := o) (d.mem (frame answer ++ carry) [] [] [] h') d.wire true
  have pc := Executes.push (answer := d.io) (o := o) (d.mem (true :: (frame answer ++ carry)) [] [] [] h') d.ctrl true
  simp only [Ports.push_wire] at pw
  simp only [Ports.push_ctrl] at pc
  have full := Executes.seq u (Executes.seq send (Executes.seq b (Executes.seq pw pc)))
  have cost : 10*packet.length+8*answer.length+15 = (7*packet.length+6) +
    ((3*packet.length+2+answer.length) + ((7*answer.length+5) + (1+1))) := by omega
  change Executes d.io o (askWord d) (d.mem (frame packet ++ carry) [] [] [] h)
    (d.mem (true :: (frame answer ++ carry)) [] [true] [] h') (10*packet.length+8*answer.length+15)
  rw [cost]
  exact full

def body (d : Ports k) (pureStep : BitCode k) : BitCode k :=
  .seq pureStep (.cases d.wire .skip (drain d.wire) (askWord d))

def loop (d : Ports k) (pureStep : BitCode k) : BitCode k := .loop d.ctrl .skip (body d pureStep)

def code (d : Ports k) (pureStep : BitCode k) : BitCode k :=
  .seq (.push d.wire false) (.seq (.push d.ctrl true) (loop d pureStep))

/-- A finite adaptive run. Bounds apply only to the actual states and packets encountered,
including the complete final output and all reply words. -/
inductive Session (ei : I → Word) (ec : C → Word) (dispatch : I ⊕ (Word × C) → Word ⊕ (Word × C))
    (oracle : WordOracle) (L : ℕ) : I ⊕ (Word × C) → Transcript → Word → Transcript → ℕ → Prop where
  | done {s history out} (step : dispatch s = .inl out) (hs : (stateCode ei ec s).length ≤ L)
      (length : out.length ≤ L) : Session ei ec dispatch oracle L s history out history 1
  | query {s history packet carry out final count} (step : dispatch s = .inr (packet,carry))
      (hs : (stateCode ei ec s).length ≤ L) (send : packet.length ≤ L)
      (receive : (oracle history packet).length ≤ L)
      (tail : Session ei ec dispatch oracle L (.inr (oracle history packet,carry))
        ((packet,oracle history packet)::history) out final count) :
      Session ei ec dispatch oracle L s history out final (count+1)

private theorem done_body (d : Ports k) {pureStep : BitCode k} {o : WordOracle} {m h n out}
    (hr : Executes d.io o pureStep m (d.mem (false::out) [] [] [] h) n) :
    Executes d.io o (body d pureStep) m (d.mem [] [] [] out.reverse h) (n+(1+(2*out.length+1))) := by
  have drainRun : Executes d.io o (drain d.wire) (d.mem out [] [] [] h) (d.mem [] [] [] out.reverse h)
      (2*out.length+1) := by simpa [Memory.drained,Ports.mem] using drain_exec d.wire d.io o (d.mem out [] [] [] h)
  apply Executes.seq hr
  apply Executes.casesFalse (xs := out) (by simp [Ports.mem]); simpa using drainRun

private theorem ask_body (d : Ports k) {pureStep : BitCode k} {o : WordOracle} {m h n packet c}
    (hr : Executes d.io o pureStep m (d.mem (true :: (frame packet ++ c)) [] [] [] h) n) :
    let reply := o h packet
    Executes d.io o (body d pureStep) m
      (d.mem (true :: (frame reply ++ c)) [] [true] [] ((packet,reply)::h))
      (n+(1+(10*packet.length+8*reply.length+15))) := by
  apply Executes.seq hr
  apply Executes.casesTrue (xs := frame packet ++ c) (by simp [Ports.mem]); simpa using askWord_exec d o packet c h

theorem loop_exec (d : Ports k) (pureStep : BitCode k) (ei : I → Word) (ec : C → Word)
    (dispatch : I ⊕ (Word × C) → Word ⊕ (Word × C)) (o : WordOracle) (L P : ℕ)
    (stepRuns : ∀ s h, (stateCode ei ec s).length ≤ L → ∃ n ≤ P, Executes d.io o pureStep
      (d.mem (stateCode ei ec s) [] [] [] h) (d.mem (actionCode ec (dispatch s)) [] [] [] h) n)
    {s h out hist rounds} (session : Session ei ec dispatch o L s h out hist rounds) :
    ∃ n ≤ rounds*(P+18*L+18), Executes d.io o (loop d pureStep)
      (d.mem (stateCode ei ec s) [] [true] [] h) (d.mem [] [] [] out.reverse hist) n := by
  induction session with
  | @done s h out hr hlen ho =>
    obtain ⟨n,hn,run⟩ := stepRuns s h hlen
    rw [hr] at run
    have finish := done_body d (out := out) run
    refine ⟨1 + ((n+(1+(2*out.length+1)))+1), by simp; omega, ?_⟩
    apply Executes.loopTrue (xs := []) (by simp [Ports.mem])
    · simpa using finish
    · exact Executes.loopNil (by simp [Ports.mem])
  | @query s h packet carry out f r hr hlen hw ha _ ih =>
    obtain ⟨n,hn,run⟩ := stepRuns s h hlen
    obtain ⟨z,hz,tail⟩ := ih
    rw [hr] at run
    have step := ask_body d (packet := packet) (c := ec carry) run
    refine ⟨1+((n+(1+(10*packet.length+8*(o h packet).length+15)))+z),?_,?_⟩
    · rw [Nat.add_mul r 1,Nat.one_mul]; omega
    · apply Executes.loopTrue (xs := []) (by simp [Ports.mem]); simpa using step; exact tail

theorem computes (d : Ports k) (pureStep : BitCode k) (ei : I → Word) (ec : C → Word)
    (dispatch : I ⊕ (Word × C) → Word ⊕ (Word × C)) (o : WordOracle) (L P : ℕ)
    (stepRuns : ∀ s h, (stateCode ei ec s).length ≤ L → ∃ n ≤ P, Executes d.io o pureStep
      (d.mem (stateCode ei ec s) [] [] [] h) (d.mem (actionCode ec (dispatch s)) [] [] [] h) n)
    {x out hist rounds} (session : Session ei ec dispatch o L (.inl x) [] out hist rounds) :
    ((code d pureStep).compile d.wire d.io).ComputesWithin o (ei x) (rounds*(P+18*L+18)+3)
      (fun h w => h = hist ∧ w = out) := by
  obtain ⟨used,limited,run⟩ := loop_exec d pureStep ei ec dispatch o L P stepRuns session
  have pt := Executes.push (answer := d.io) (o := o) (d.mem (ei x) [] [] [] []) d.wire false
  have pc := Executes.push (answer := d.io) (o := o) (d.mem (false::ei x) [] [] [] []) d.ctrl true
  simp only [Ports.push_wire] at pt
  simp only [Ports.push_ctrl] at pc
  have all := Executes.seq pt (Executes.seq pc run)
  rw [← d.source_start] at all
  apply compile_computes (c := code d pureStep) all (by omega)
  simp [Ports.mem]

end WordDialogue
end OracleSpec
end LinearProgramming
end Optimization
end OAI
