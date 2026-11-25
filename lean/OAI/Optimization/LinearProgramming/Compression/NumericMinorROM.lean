import OAI.Optimization.LinearProgramming.Compression.NumericROMCore
import OAI.Optimization.LinearProgramming.Compression.NumericROMScatter
import OAI.Optimization.LinearProgramming.Compression.InnerNativeInput

/-! The closed native minor subroutine. Its only inputs are the four ordinary address
words and the positive rational magnitudes. It computes all proxies, constructs and
executes the inner bit program, and physically publishes its restart or rational result. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable MinorProxyCache SignWire OracleSpec Polynomial
namespace NumericROM

noncomputable def numericalPrefix : Fragment :=
  .seq (scatterPrefix numericInnerClock) (.ofBlock (BitRAM.installControlInput Inner.machine Inner.Metadata.writeInputBlock))

noncomputable def setupTime : Polynomial ℕ :=
  scatterTime numericInnerClock+300*(X+(X+1)^6+1)^2+C Inner.machine.stackCount+100

/-- Initialize the BitRAM itself from actual input address words in the same memory
that holds the resident numerical oracle. -/
theorem numericalPrefix_correct : PrefixSpec numericalPrefix setupTime := by
  intro n g rank member mag width hr hp
  let P := fun x : ℚ => ratBits x≤workingHeight numericInnerClock n mag
  let cap := physicalCap numericInnerClock n
  obtain ⟨raw,setup,sc⟩ := scatterPrefix_run numericInnerClock rank member mag width hr hp
  have positiveLimit : 3≤workingHeight numericInnerClock n mag := by
    have h := (height_dominates n (inputHeight mag) (numericInnerClock.eval n) (g+1)
      (manuscriptProxyFuel n) (numericCachePrecision n)).2.2
    exact (show 3≤2*numericInnerClock.eval n+7 by omega).trans h
  have outside : 2*cap<raw.index BitRAM.recvBaseReg := by
    change 2*cap<raw.index 47
    rw [sc.ports.answer]
    unfold callbackReply callbackRow callbackSend
    dsimp only [cap]
    omega
  have room := physicalCap_room numericInnerClock width (rowBase n g) sc.row
  have capHigh : 135≤cap := by dsimp only [cap];omega
  obtain ⟨k,hk,t,load,vm,effect⟩ := Inner.installControlInput_correct (P := P) Inner.machine raw n g member rank
    setup.safe_end (show P 0 from positiveLimit) (show P 1 from positiveLimit) (by
      change 2*cap < raw.index 47 at outside
      omega)
    sc.dimension sc.generators sc.membership sc.rankAt hr
  have ports := sc.ports.transfer (fun i hi => effect.headers i (by omega) (by omega)
    (by change i≠49;omega))
  have resident := sc.resident.transferWindow (fun i hi upto => effect.data (2*i) (by omega) (Or.inl (by omega))) effect.even
  have growth : n+g+1≤n+(n+1)^6+1 := by change g≤(n+1)^6 at width;omega
  refine ⟨t,(setup.seq (Fragment.Run.ofBlock (P := P) load)).mono ?_,vm,ports,resident,sc.capacity,sc.code,sc.row⟩
  have clock : k≤300*(n+(n+1)^6+1)^2+Inner.machine.stackCount+100 := hk.trans
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left growth 2)) _) _)
  simp only [setupTime,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_one,eval_ofNat]
  omega

end NumericROM

/-- A single RAM ROM for the complete adaptive numerical minor query, independent of
matrix or query dimensions, coefficients, and the mathematical response. -/
noncomputable def numericMinorROM : Program :=
  prefixLinkedTaggedFlatReply NumericROM.numericalPrefix Inner.machine wordComparator

noncomputable def numericMinorTime : Polynomial ℕ :=
  NumericROM.time NumericROM.setupTime numericInnerClock Inner.machine.states

noncomputable def numericMinorHeight : Polynomial ℕ := NumericROM.height numericInnerClock

/-- Ordinary normal entry, dimension-polynomial elapsed instructions, bounded-height
intermediate rationals, and exact, fully exposed reduced numerator and denominator. -/
theorem numericMinorROM_correct : NumericSolverSpec numericMinorROM numericMinorTime numericMinorHeight :=
  NumericROM.solver_of_prefix NumericROM.numericalPrefix_correct

end Compression
end LinearProgramming
end Optimization
end OAI
