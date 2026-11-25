import OAI.Optimization.LinearProgramming.OracleSpec.Machine

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace Dispatch
open OracleSpec

def chargedAsk {p : BitProgram} (o : WordOracle) (c : p.Config) :=
  1+c.bufferRev.reverse.length+(o c.transcript c.bufferRev.reverse).length

def answered {p : BitProgram} (o : WordOracle) (c : p.Config) (q : Fin p.states) : p.Config :=
  let word := c.bufferRev.reverse
  let bits := o c.transcript word
  { pc := some q, store := Function.update c.store p.answerStack bits, bufferRev := [],
    transcript := (word,bits)::c.transcript }

theorem tick_ask {p : BitProgram} {bo : WordOracle} {c : p.Config} {q q' : Fin p.states}
    (pc : c.pc = some q) (ask : p.instruction q (c.store (p.scan q)).head? = .ask q') :
    p.tick bo c = some (chargedAsk bo c, answered bo c q') := by
  simp [BitProgram.tick,pc,ask,chargedAsk,answered]

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI
