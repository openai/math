import OAI.Optimization.LinearProgramming.OracleSpec.CompilerProof
import Lean.Elab.Tactic.Omega

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace BitCode

variable {k : ℕ}

/-- Copy a word from a work stack, emitting its bits in top-to-bottom order. -/
def drain (stack : Fin k) : BitCode k := .loop stack (.emit false) (.emit true)

def Memory.drained (m : Memory k) (s : Fin k) : Memory k where
  store := Function.update m.store s []
  bufferRev := (m.store s).reverse ++ m.bufferRev
  transcript := m.transcript

theorem drain_exec (s answer : Fin k) (o : WordOracle) (m : Memory k) :
    Executes answer o (drain s) m (m.drained s) (2 * (m.store s).length + 1) := by
  generalize hs : m.store s = xs
  induction xs generalizing m with
  | nil =>
    have hu : Function.update m.store s [] = m.store := by rw [← hs, Function.update_eq_self]
    have hm : m.drained s = m := by simp [Memory.drained, hs, hu]
    simpa [hm, drain] using Executes.loopNil (answer := answer) (o := o)
      (p := .emit false) (q := .emit true) hs
  | cons b xs ih =>
    let next := (m.pop s).emit b
    have hn : next.store s = xs := by simp [next, Memory.pop, Memory.emit, hs]
    have rest := ih next hn
    have finish : next.drained s = m.drained s := by
      simp [Memory.drained, next, Memory.pop, Memory.emit, hs, List.append_assoc]
    rw [finish] at rest
    have length : 2 * (b :: xs).length + 1 = 1 + (1 + (2 * xs.length + 1)) := by
      simp only [List.length_cons]; omega
    rw [length]
    cases b with
    | false => exact Executes.loopFalse hs (Executes.emit _ _) rest
    | true => exact Executes.loopTrue hs (Executes.emit _ _) rest

/-- Transmit exactly the word in `s`. The full copying and oracle I/O charge is included. -/
def queryFromStack (s : Fin k) : BitCode k := .seq (drain s) .ask

theorem queryFromStack_exec (s answer : Fin k) (o : WordOracle) (m : Memory k)
    (h : m.bufferRev = []) :
    let packet := m.store s
    let response := o m.transcript packet
    Executes answer o (queryFromStack s) m ((m.drained s).receive answer response)
      (3 * packet.length + 2 + response.length) := by
  dsimp only
  have first := drain_exec s answer o m
  have second : Executes answer o .ask (m.drained s)
      ((m.drained s).receive answer (o m.transcript (m.store s)))
      (1 + (m.store s).length + (o m.transcript (m.store s)).length) := by
    simpa [Memory.drained, h] using Executes.ask (answer := answer) (o := o) (m.drained s)
  rw [show 3 * (m.store s).length + 2 + (o m.transcript (m.store s)).length =
    (2 * (m.store s).length + 1) + (1 + (m.store s).length + (o m.transcript (m.store s)).length) by omega]
  exact Executes.seq first second

end BitCode
end OracleSpec
end LinearProgramming
end Optimization
end OAI
