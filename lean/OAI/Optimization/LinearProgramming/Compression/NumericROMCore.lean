import OAI.Optimization.LinearProgramming.Compression.NumericROMSetup
import OAI.Optimization.LinearProgramming.Compression.SignWireImplements
import OAI.Optimization.LinearProgramming.Compression.NumericROMLogic
import OAI.Optimization.LinearProgramming.Compression.BinaryWireLinked

/-! Compose the physically prepared initial bit-machine and numerical cache with the
actual mixed-sign callback and public restart/rational-word exit. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace NumericROM

open RAM RAM.Callable MinorProxyCache SignWire OracleSpec OracleSpec.MinorLog
open scoped BigOperators

structure Ready {g : ℕ} (n rank : ℕ) (member : Bool) (mag : Fin (g+1) → ℚ) (m : Memory ℚ) : Prop where
  vm : BitRAM.Rep Inner.machine (Inner.machine.initial (Inner.inputWord n g member rank)) m
  ports : PublicPorts (g+2) (callbackSend (physicalCap numericInnerClock n))
    (callbackReply (g+1) (manuscriptProxyFuel n) (physicalCap numericInnerClock n))
    (callbackRow (g+1) (manuscriptProxyFuel n) (physicalCap numericInnerClock n)) (rowBase n g) m
  cache : ResidentHigh (n:=g+1) (tapeMagnitude mag) (numericProxyCacheBuffers n g)
    (manuscriptProxyFuel n) (numericCachePrecision n) (budgetC n g) (firstR n) (physicalCap numericInnerClock n)
    (rowBase n g) (fun x => ratBits x≤workingHeight numericInnerClock n mag) m
  capacity : budgetC n g≤firstR n
  address : addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14)))≤firstR n
  row : rowBase n g≤firstR n

/-- A counted setup must begin on the literal public argument arrays and establish
both physical states in the same memory. -/
def PrefixSpec (front : Fragment) (setup : Polynomial ℕ) : Prop :=
  ∀ {n g : ℕ} (rank : ℕ) (member : Bool) (mag : Fin (g+1)→ℚ), g≤paperWidth n → rank≤g →
    (∀i,0 < mag i) → ∃ m, front.Run (fun x => ratBits x≤workingHeight numericInnerClock n mag)
      (start [n,g,member.toNat,rank] (List.ofFn mag)).memory (setup.eval n) m ∧ Ready n rank member mag m

/-- All later stages are here fixed: the actual interpreter for the full inner machine,
the actual numerical word comparator, and the explicit reduced rational publication. -/
theorem solver_of_prefix {front : Fragment} {setup : Polynomial ℕ} (configured : PrefixSpec front setup) :
    NumericSolverSpec (prefixLinkedTaggedFlatReply front Inner.machine wordComparator)
      (time setup numericInnerClock Inner.machine.states) (height numericInnerClock) := by
  intro n g hg position rank hr hit mag hp
  let d := g+1
  let f := manuscriptProxyFuel n
  let prec := numericCachePrecision n
  let cap := physicalCap numericInnerClock n
  let b := rowBase n g
  let q := numericInnerClock.eval n
  let r := numericalValue n position mag
  obtain ⟨m,prep,ready⟩ := configured rank position.isSome mag hg hr hp
  have total : 2*(firstR n+(q+1)*(cachedProxySignSteps d f (budgetC n g)+5))+135+2*(b+g+2)≤cap :=
    physicalCap_room numericInnerClock hg b ready.row
  have reserve : 2*(firstR n+(q+1)*(cachedProxySignSteps d f (budgetC n g)+5))+1≤cap := by omega
  have rowRoom : 2*(b+d)+1≤cap := by dsimp only [d];omega
  have arena := callbackArena_standard d f cap b (by omega) rowRoom
  have service := wordComparator_implements Inner.machine d f prec (queryHeight numericInnerClock n mag) (budgetC n g)
    (firstR n) (q+1) cap (callbackRow d f cap) b (callbackSend cap) (callbackReply d f cap)
    (Inner.coefficientCap n) (tapeMagnitude mag) (numericProxyCacheBuffers n g)
    (queryHeight_bound numericInnerClock n mag) (Inner.coefficientCap_scaled n).le le_rfl ready.capacity ready.address reserve arena
  obtain ⟨⟨steps,hs,last,run,halt,out⟩,valid,hword⟩ := numericInner_run hg position rank hr hit mag hp
  have initial : CallbackContext d f prec (queryHeight numericInnerClock n mag) (budgetC n g) (firstR n) cap (callbackRow d f cap) b
      (callbackSend cap) (callbackReply d f cap) (tapeMagnitude mag) (numericProxyCacheBuffers n g) [] m := by
    refine ⟨ready.ports,?_⟩
    simpa only [List.length_nil,Nat.zero_mul,Nat.add_zero,d,f,prec,cap,b,workingHeight] using ready.cache
  have heightRoom := (height_dominates n (inputHeight mag) q d f prec).2.2
  have lengthRoom : 2*(Inner.outputWord r).length+7≤workingHeight numericInnerClock n mag :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hword) 7).trans heightRoom
  obtain ⟨t,⟨k,hk,tr,ht,finished,allValues⟩,emission⟩ := prefixLinkedTaggedFlatReply_call prep service run halt valid
    ready.vm initial r out lengthRoom
  have clock := time_le setup numericInnerClock Inner.machine.states n g steps (Inner.outputWord r).length hg hs hword
  have timeOK : k≤(time setup numericInnerClock Inner.machine.states).eval n := by
    apply hk.trans
    simpa only [linkedDriverClock,Nat.add_assoc,d,f,budgetC,Inner.outputWord] using clock
  have bitsOK := height_le numericInnerClock n (inputHeight mag) g hg
  exact ⟨t,⟨k,timeOK,tr,ht,finished,fun i j => (allValues i j).trans bitsOK⟩,emission⟩

end NumericROM
end Compression
end LinearProgramming
end Optimization
end OAI
