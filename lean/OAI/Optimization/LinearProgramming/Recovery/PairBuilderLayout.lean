import OAI.Optimization.LinearProgramming.RAM.Code

/-! Actual low-bank arguments of the complementary-basis and witness-table callers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder

open RAM

structure Layout (h n : ℕ) where
  src : ℕ
  out : ℕ
  scratch : ℕ
  previous : ℕ
  minimum : 256 ≤ src
  sourceRoom : src+h*n ≤ out
  outputRoom : out+n*n ≤ scratch

structure InputRegs {K : Type} {h n : ℕ} (l : Layout h n) (m : Memory K) : Prop where
  height : m.index 200=h
  width : m.index 201=n
  source : m.index 202=l.src
  target : m.index 203=l.out
  workspace : m.index 204=l.scratch
  previous : m.index 205=l.previous

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
