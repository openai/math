import OAI.Optimization.LinearProgramming.OracleSpec.Compiler

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec

namespace BitProgram.Run

theorem single {p : BitProgram} {o : WordOracle} {c d : p.Config} {k : ℕ}
    (h : p.tick o c = some (k,d)) : p.Run o c k d := by
  simpa only [Nat.add_zero] using step h (refl d)

theorem append {p : BitProgram} {o : WordOracle} {a b c : p.Config} {i j : ℕ}
    (h : p.Run o a i b) (h' : p.Run o b j c) : p.Run o a (i+j) c := by
  induction h with
  | refl => simpa using h'
  | step ht _ ih => simpa only [Nat.add_assoc] using step ht (ih h')

end BitProgram.Run

namespace BitCode

variable {k : ℕ}

def place (p : BitProgram) (q : Fin p.states) (m : Memory p.stackCount) : p.Config :=
  ⟨some q, m.store, m.bufferRev, m.transcript⟩

def perform (p : BitProgram) (o : WordOracle) (m : Memory p.stackCount) :
    BitInstruction (Fin p.states) (Fin p.stackCount) → ℕ × p.Config
  | .jump q => (1, place p q m)
  | .push s b q => (1, place p q (m.push s b))
  | .pop s q => (1, place p q (m.pop s))
  | .emit b q => (1, place p q (m.emit b))
  | .ask q => let packet := m.bufferRev.reverse; let response := o m.transcript packet
      (1+packet.length+response.length, place p q (m.receive p.answerStack response))
  | .halt => (1, ⟨none, m.store, m.bufferRev, m.transcript⟩)

/-- A code fragment may be embedded in any enclosing finite program, with any return address. -/
def Represents (p : BitProgram) (defaultStack : Fin p.stackCount) (c : BitCode p.stackCount)
    (dest : Fin p.states) (w : c.Node → Fin p.states) : Prop :=
  ∀ i, p.scan (w i) = (line defaultStack c dest w i).scan ∧
       p.instruction (w i) = (line defaultStack c dest w i).op

theorem executesLine {p : BitProgram} {o : WordOracle} {defaultStack : Fin p.stackCount}
    {c : BitCode p.stackCount} {dest w} (h : Represents p defaultStack c dest w)
    (i : c.Node) (m : Memory p.stackCount) :
    let l := line defaultStack c dest w i
    let next := perform p o m (l.op (m.store l.scan).head?)
    p.Run o (place p (w i) m) next.1 next.2 := by
  apply BitProgram.Run.single
  obtain ⟨hs, hi⟩ := h i
  unfold BitProgram.tick place
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hs, hi]
  cases (line defaultStack c dest w i).op (m.store (line defaultStack c dest w i).scan).head? <;> rfl

/-- Structured executions compile to the literal machine with exactly the same step cost.
The proof is parametric in the surrounding program and in the target continuation. -/
theorem Executes.toMachine {p : BitProgram} {o : WordOracle} {c : BitCode p.stackCount}
    {m t : Memory p.stackCount} {n : ℕ} (hr : Executes p.answerStack o c m t n) :
    ∀ (base : Fin p.stackCount) (dest : Fin p.states) (w : c.Node → Fin p.states),
      Represents p base c dest w → p.Run o (place p (w c.entry) m) n (place p dest t) := by
  induction hr with
  | skip m =>
    intro base dest w h
    exact executesLine h () m
  | push m s b =>
    intro base dest w h
    exact executesLine h () m
  | emit m b =>
    intro base dest w h
    exact executesLine h () m
  | ask m =>
    intro base dest w h
    exact executesLine h () m
  | @seq a b m mid out ka kb _ _ iha ihb =>
    intro base dest w h
    exact (iha base (w (.inr b.entry)) (w ∘ Sum.inl) (fun i => h (.inl i))).append
      (ihb base dest (w ∘ Sum.inr) (fun i => h (.inr i)))
  | @casesNil s a b c m out k hs _ ih =>
    intro base dest w h
    have first := executesLine (o := o) h (.inl ()) m
    simp only [line, hs, List.head?_nil, perform] at first
    exact first.append (ih base dest (w ∘ Sum.inr ∘ Sum.inl) (fun i => h (.inr (.inl i))))
  | @casesFalse s a b c m out xs k hs _ ih =>
    intro base dest w h
    have first := executesLine (o := o) h (.inl ()) m
    simp only [line, hs, List.head?_cons, perform] at first
    exact first.append (ih base dest (w ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl)
      (fun i => h (.inr (.inr (.inl i)))))
  | @casesTrue s a b c m out xs k hs _ ih =>
    intro base dest w h
    have first := executesLine (o := o) h (.inl ()) m
    simp only [line, hs, List.head?_cons, perform] at first
    exact first.append (ih base dest (w ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr)
      (fun i => h (.inr (.inr (.inr i)))))
  | @loopNil s a b m hs =>
    intro base dest w h
    have first := executesLine (o := o) h (.inl ()) m
    simpa only [line, hs, List.head?_nil, perform, entry] using first
  | @loopFalse s a b m mid out xs ka kb hs _ _ iha ihloop =>
    intro base dest w h
    have first := executesLine (o := o) h (.inl ()) m
    simp only [line, hs, List.head?_cons, perform] at first
    exact first.append ((iha base (w (.inl ())) (w ∘ Sum.inr ∘ Sum.inl)
      (fun i => h (.inr (.inl i)))).append (ihloop base dest w h))
  | @loopTrue s a b m mid out xs ka kb hs _ _ ihb ihloop =>
    intro base dest w h
    have first := executesLine (o := o) h (.inl ()) m
    simp only [line, hs, List.head?_cons, perform] at first
    exact first.append ((ihb base (w (.inl ())) (w ∘ Sum.inr ∘ Sum.inr)
      (fun i => h (.inr (.inr i)))).append (ihloop base dest w h))

private theorem represents_compile (c : BitCode k) (input answer : Fin k) :
    Represents (c.compile input answer) input c c.exitAddress c.address := by
  intro i
  simp [compile, table, address]

def startMemory (input : Fin k) (bits : Word) : Memory k :=
  ⟨fun s => if s = input then bits else [], [], []⟩

/-- From a concrete big-step proof one obtains the finite program required by the oracle
complexity statements. A single final `halt` supplies the extra charged step. -/
theorem compile_computes {c : BitCode k} {input answer : Fin k} {bits : Word} {o : WordOracle}
    {post : Transcript → Word → Prop} {m : Memory k} {n bound : ℕ}
    (h : Executes answer o c (startMemory input bits) m n) (hn : n + 1 ≤ bound)
    (hp : post m.transcript m.bufferRev.reverse) :
    (c.compile input answer).ComputesWithin o bits bound post := by
  let p := c.compile input answer
  have run : p.Run o (p.initial bits) n (place p c.exitAddress m) := by
    change p.Run o (place p (c.address c.entry) (startMemory input bits)) n _
    exact Executes.toMachine (p := p) (o := o) (c := c) h input c.exitAddress c.address
      (represents_compile c input answer)
  let stopped : p.Config := ⟨none, m.store, m.bufferRev, m.transcript⟩
  have last : p.Run o (place p c.exitAddress m) 1 stopped := by
    apply BitProgram.Run.single
    simp [p, place, stopped, BitProgram.tick, compile, table, exitAddress]
  exact ⟨n+1, stopped, run.append last, hn, rfl, hp⟩

end BitCode
end OracleSpec
end LinearProgramming
end Optimization
end OAI
