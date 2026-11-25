import OAI.Optimization.LinearProgramming.RAM.CallableRawTapes
import OAI.Optimization.LinearProgramming.Recovery.WitnessTableCore
import OAI.Optimization.LinearProgramming.Recovery.MaskedLayout
import OAI.Optimization.LinearProgramming.Recovery.DenseEncoding

/-! The normalized-equation solver receives its usual serialized tapes from the
same masked matrix and header produced by the ordinary support routine. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessTable

open RAM RAM.Callable Geometry

/-- The tableau contains the right-hand side first and then the columns of the
support equations augmented by the marked coordinate fixed to one. The
returned input descriptor can be passed directly to the equation solver. -/
theorem program_run {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {h n : ℕ}
    (C : Matrix (Fin (h+n)) (Fin n) K) (hn : 0 < n)
    (P : K → Prop) (m : Memory K) (hm : m.AllData P) (h0 : P 0) (h1 : P 1)
    (regs : PairBuilder.InputRegs (MaskedInput.pairLayout h n) m)
    (input : uniformRect (h+n) n (MaskedInput.base h n) m = C) :
    ∃ t steps, steps ≤ clockPolynomial.eval (h+n) ∧
      Block.Eval (Memory.AllData P) block m steps t ∧
      RawTapes t (tableBase h n) 208 (capacity h n) (encodedGramInput (matrix C hn)) [n+1,h+n+1] ∧
      t.index 210 = destination h n ∧ t.index 211 = n := by
  obtain ⟨t,k,hk,run,table,header⟩ :=
    execute C hn P m hm h0 h1 regs.height regs.width regs.source regs.target input
  refine ⟨t,k,hk,run,?_,header.next,header.originalWidth⟩
  refine ⟨header.scalarBase,?_,header.addressBase,header.addressLength,header.bound,
    PairBuilder.dense_encoded t _ table,?_⟩
  · simpa [words] using header.scalarLength
  · intro j hj
    rcases j with _|j
    · simpa using header.firstDim
    · rcases j with _|j
      · simpa using header.secondDim
      · simp at hj

end WitnessTable
end Recovery
end LinearProgramming
end Optimization
end OAI
