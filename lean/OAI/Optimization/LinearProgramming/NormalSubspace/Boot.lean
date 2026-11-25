import OAI.Optimization.LinearProgramming.NormalSubspace.Placement
import OAI.Optimization.LinearProgramming.RAM.CallableReentrant
import OAI.Optimization.LinearProgramming.RAM.CallableOddCalls
import OAI.Optimization.LinearProgramming.RAM.CallableOddLeaf
import OAI.Optimization.LinearProgramming.Recovery.NumericCall
import OAI.Optimization.LinearProgramming.Geometry.BorderService
import OAI.Optimization.LinearProgramming.RAM.CallableWindow

/-! Typed subspace initialization inside the numeric bank of the public PCG solver.
The service initializer is invoked on its genuine three-word native header and the two
original scalar matrices. Its exact final memory is retained across the geometric setup. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace

open RAM RAM.Callable Geometry Geometry.LabelInput Geometry.BorderBatch Recovery.PriceLayout Polynomial

/-- The service returns through an address tag in disposable geometric register 30. -/
def numericInitialize (init : Program) (packetC packetE : Nat) : Fragment :=
  .seq (Odd.leaf (geometryHeaders packetC packetE))
    (.seq (Fragment.stage (Fragment.invoke init 1 (Odd.sink (.index 30)))) (Odd.leaf placeMatrices))

noncomputable def numericInitCost (c e clock n : Nat) :=
  4*(geometryHeaderTime c e).eval n + (19*(n*n+4)+225+(2*clock+2)+4*(14*(n*n)+13))

noncomputable def numericInitPolynomial (c e : Nat) (clock : Polynomial Nat) : Polynomial Nat :=
  4*geometryHeaderTime c e + (19*(X*X+4)+225+(2*clock+2)+4*(14*(X*X)+13))

theorem numericInitPolynomial_eval (c e : Nat) (clock : Polynomial Nat) (n : Nat) :
    (numericInitPolynomial c e clock).eval n=numericInitCost c e (clock.eval n) n := by
  simp only [numericInitPolynomial,numericInitCost,eval_add,eval_mul,eval_X,eval_ofNat]

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r s : Nat}

/-- The concrete service trace determines the native memory, and even register zero of
the original scalar input can be arbitrary. The same relocatable code accepts every
dimension pair. -/
theorem numericInitialize_correct (init : Program) (packetC packetE clock : Nat)
    (D : Matrix (Fin r) (Fin (r+s)) K) (E : Matrix (Fin s) (Fin (r+s)) K) (ready : State K)
    (P : K → Prop) {k : Nat} (tr : Fin (k+1) → State K) (hk : k ≤ clock)
    (nativeRun : Trace init (start [r,s,r+s] (rawWords D E)) k tr)
    (last : tr (Fin.last k)=ready) (halt : ready.output=some 0) (safe : ∀ i j, P ((tr i).data j)) :
    let raw := (start [r,s] (rawWords D E)).memory
    let empty := (start [] ([] : List K)).memory
    let x := buffers r s (r+s) (polyBound packetC packetE (r+s))
    ∃ geom, (numericInitialize init packetC packetE).Run P (Odd.memory empty raw)
      (numericInitCost packetC packetE clock (r+s)) (Odd.memory ready.memory geom) ∧ Matrices x D E geom := by
  let n := r+s
  let xs := rawWords D E
  let raw := (start [r,s] xs).memory
  let empty := (start [] ([] : List K)).memory
  let L := r*n+s*n
  have len : xs.length=L := rawWords_length D E
  have square : L=(r+s)*(r+s) := (Nat.add_mul r s n).symm
  have rawSafe (i : Nat) : P (raw.data i) := by
    change P ((start [r,s,n] xs).data i)
    rw [←nativeRun.1]
    exact safe 0 i
  have p0 : P 0 := by
    have h := rawSafe xs.length
    simpa [raw,State.memory,start] using h
  have clearSafe : empty.AllData P := by intro i;simpa [empty,State.memory,start] using p0
  have clearFoot : Footprint 0 (start [] ([] : List K)) := Footprint.initial [] [] (by simp) (by simp) (by simp)
  obtain ⟨h,c,header,hc,unchanged,pos⟩ := geometryHeaders_correct packetC packetE r s xs rawSafe
  have setup := Odd.leaf_run P empty clearSafe header
  have data (j : Nat) : h.data j=xs[j]?.getD 0 := congrFun unchanged j
  have tapes : RawTapes h 0 0 (L+4) xs [r,s,n] := pos.rawTapes xs len data
  have hhalt : (tr (Fin.last k)).output=some 0 := last ▸ halt
  have hs := Odd.invoke_packed 1 (.index 30) P h [r,s,n] xs tr (by decide : 0<1)
    header.safe_end nativeRun safe hhalt (show (h.putIndex 30 0).AllData P from header.safe_end)
  rw [last] at hs
  have call := Fragment.stage_of_run (start [] ([] : List K)) h 0 0 0 (L+4) xs [r,s,n] tapes header.safe_end
    clearSafe p0 clearFoot (by omega) (by omega) (by simp)
    (show (Fragment.invoke init 1 (Odd.sink (.index 30))).Run P (Odd.memory (start [r,s,n] xs).memory h)
      (2*k+2) (Odd.memory ready.memory (h.putIndex 30 0)) from hs)
  have nativeSafe : ready.memory.AllData P := fun j => last ▸ safe (Fin.last k) j
  obtain ⟨geom,v,hv,placed,matrices⟩ := placeMatrices_correct D E (polyBound packetC packetE n)
    (h.putIndex 30 0) (show (h.putIndex 30 0).AllData P from header.safe_end) pos.afterReturn data
  have keep := Odd.leaf_run P ready.memory nativeSafe placed
  refine ⟨geom,(setup.seq (call.seq keep)).mono ?_,matrices⟩
  unfold numericInitCost
  omega

/-- The exact normalized rational initializer promised by the online minor-service
theorem can be plugged in directly, retaining its scalar-height guarantee verbatim. -/
theorem numericInitialize_service (init : Program) (packetC packetE : Nat)
    (D : Matrix (Fin r) (Fin (r+s)) ℚ) (E : Matrix (Fin s) (Fin (r+s)) ℚ)
    (S : Service D E) (P : ℚ → Prop)
    (initial : OracleSpec.MinorLog.call init S.clock S.height
      (start [r,s,r+s] (OracleSpec.MinorLog.entries D++OracleSpec.MinorLog.entries E)) S.ready)
    (done : S.ready.output=some 0) (allowed : ∀ q : ℚ, ratBits q ≤ S.height → P q) :
    let raw := (start [r,s] (OracleSpec.MinorLog.entries D++OracleSpec.MinorLog.entries E)).memory
    let empty := (start [] ([] : List ℚ)).memory
    let x := buffers r s (r+s) (polyBound packetC packetE (r+s))
    ∃ geom, (numericInitialize init packetC packetE).Run P (Odd.memory empty raw)
      (numericInitCost packetC packetE S.clock (r+s)) (Odd.memory S.ready.memory geom) ∧ Matrices x D E geom := by
  obtain ⟨k,hk,tr,run,last,safe⟩ := initial
  have h := numericInitialize_correct init packetC packetE S.clock D E S.ready P tr hk
    (by simpa only [rawWords_rational] using run) last done (fun i j => allowed _ (safe i j))
  simpa only [rawWords_rational] using h

/-- The actual initialized native state has a finite dimension-polynomial footprint. -/
theorem service_ready_footprint (init : Program)
    (D : Matrix (Fin r) (Fin (r+s)) ℚ) (E : Matrix (Fin s) (Fin (r+s)) ℚ) (S : Service D E)
    (initial : OracleSpec.MinorLog.call init S.clock S.height
      (start [r,s,r+s] (OracleSpec.MinorLog.entries D++OracleSpec.MinorLog.entries E)) S.ready) :
    Footprint (addressBudget init + (r+s)*(r+s) + 2*(r+s)+3+S.clock) (S.ready.memory.atPC 0) := by
  obtain ⟨k,hk,tr,run,last,_⟩ := initial
  have actual := nativeWindow_trace run hk
  rw [last] at actual
  apply actual.mono
  have len : (OracleSpec.MinorLog.entries D++OracleSpec.MinorLog.entries E).length=(r+s)*(r+s) := by
    rw [←rawWords_rational,rawWords_length,←Nat.add_mul]
  unfold nativeWindow
  simp only [len,List.length_cons,List.length_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  omega

/-- Enter the same persistent exact service/geometry memory underneath the outer bit VM.
Only its designated scratch return index receives the fixed tag. -/
theorem numericInitialize_service_under_vm (init : Program) (packetC packetE : Nat)
    (D : Matrix (Fin r) (Fin (r+s)) ℚ) (E : Matrix (Fin s) (Fin (r+s)) ℚ)
    (S : Service D E) (vm : Memory ℚ) (P : ℚ → Prop) (hvm : vm.AllData P)
    (initial : OracleSpec.MinorLog.call init S.clock S.height
      (start [r,s,r+s] (OracleSpec.MinorLog.entries D++OracleSpec.MinorLog.entries E)) S.ready)
    (done : S.ready.output=some 0) (allowed : ∀ q : ℚ, ratBits q ≤ S.height → P q) :
    let raw := (start [r,s] (OracleSpec.MinorLog.entries D++OracleSpec.MinorLog.entries E)).memory
    let empty := (start [] ([] : List ℚ)).memory
    let x := buffers r s (r+s) (polyBound packetC packetE (r+s))
    ∃ geom, (Recovery.PackedPCG.numericCall (numericInitialize init packetC packetE)).Run P
      (Odd.memory (Odd.memory empty raw) vm) (2*(numericInitCost packetC packetE S.clock (r+s)+1)+2)
      (Odd.memory (Odd.memory S.ready.memory geom) (vm.putIndex 1 0)) ∧ Matrices x D E geom := by
  obtain ⟨geom,run,matrices⟩ := numericInitialize_service init packetC packetE D E S P initial done allowed
  exact ⟨geom,Recovery.PackedPCG.numericCall_run run vm hvm,matrices⟩

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
