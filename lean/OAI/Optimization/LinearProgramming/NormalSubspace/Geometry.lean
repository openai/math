import OAI.Optimization.LinearProgramming.Geometry.RawLabelCopy
import OAI.Optimization.LinearProgramming.Geometry.RawLabelTape
import OAI.Optimization.LinearProgramming.RAM.FrameFirstHeader
import OAI.Optimization.LinearProgramming.RAM.CallableRawTapes
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

/-! Retained geometry data for normal subspace input. The raw row-major scalar matrices
are copied by genuine RAM instructions and are kept above every possible price packet. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace

open RAM RAM.Tape RAM.Call RAM.Callable Geometry Geometry.LabelInput Polynomial

variable {K : Type} {r s : Nat}

def rawWords (D : Matrix (Fin r) (Fin (r+s)) K) (E : Matrix (Fin s) (Fin (r+s)) K) : List K :=
  matrixWords D ++ matrixWords E

@[simp] theorem rawWords_length (D : Matrix (Fin r) (Fin (r+s)) K) (E : Matrix (Fin s) (Fin (r+s)) K) :
    (rawWords D E).length=r*(r+s)+s*(r+s) := by simp [rawWords]

private theorem matrixWords_entries {a n : Nat} (M : Matrix (Fin a) (Fin n) ℚ) :
    matrixWords M = OracleSpec.MinorLog.entries M := by
  have atCell (i : Fin a) (j : Fin n) (h : i.val*n+j.val < a*n) :
      (finProdFinEquiv.symm (⟨i.val*n+j.val,h⟩ : Fin (a*n)))=(i,j) := by
    have eq : (⟨i.val*n+j.val,h⟩ : Fin (a*n))=finProdFinEquiv (i,j) := by
      apply Fin.ext;change i.val*n+j.val=j.val+n*i.val;ac_rfl
    rw [eq,Equiv.symm_apply_apply]
  unfold matrixWords
  rw [List.ofFn_mul]
  simp only [OracleSpec.MinorLog.entries,atCell]

theorem rawWords_rational (D : Matrix (Fin r) (Fin (r+s)) ℚ) (E : Matrix (Fin s) (Fin (r+s)) ℚ) :
    rawWords D E=OracleSpec.MinorLog.entries D++OracleSpec.MinorLog.entries E := by
  rw [rawWords,matrixWords_entries,matrixWords_entries]

/-- The full input snapshot begins at the primal page. The relocated dual precedes it,
and the reusable price packet lies beyond both matrices. -/
def buffers (r s n T : Nat) : LabelInput.Buffers r s n :=
  let dual := 256+n*n+T
  let primal := dual+s*n
  let price := primal+(r*n+s*n)
  ⟨dual,primal,price,price+n,256,by dsimp [dual];omega,le_rfl,by dsimp [price];omega,le_rfl,by decide⟩

private def matrixPlan : HeaderPlan 227 :=
  let r : AddressTerm 227 := .reg 0
  let s : AddressTerm 227 := .reg 1
  let n : AddressTerm 227 := .reg 2
  [(2,r+s),(129,r),(130,n),(148,s),(147,256+n*n+.reg 226),
   (131,.reg 147+s*n),(224,r*n+s*n),(132,.reg 131+.reg 224),(133,.reg 132+n),(136,256),
   (206,.reg 131),(225,.reg 131+r*n),(200,.reg 147),(220,s*n),(215,0),
   (55,0),(56,.reg 224),(57,0),(58,3),(60,.reg 224+4)]

private def packetTimeTerm (C E : Nat) : AddressTerm 2 :=
  .val C * addressPower (.reg 0+.reg 1+1) E

def geometryHeaders (C E : Nat) : Block :=
  .seq ((packetTimeTerm C E).code 226) (HeaderPlan.code 227 matrixPlan)

noncomputable def geometryHeaderTime (c e : Nat) : Polynomial Nat :=
  (packetTimeTerm c e).boundCost + (HeaderPlan.budget matrixPlan).comp (X+C c*(X+1)^e)

structure GeometryHeader (r s T : Nat) (m : Memory K) : Prop where
  row0 : m.index 0=r
  row1 : m.index 1=s
  columns2 : m.index 2=r+s
  rank : m.index 129=r
  columns : m.index 130=r+s
  primal : m.index 131=(buffers r s (r+s) T).primal
  price : m.index 132=(buffers r s (r+s) T).price
  free : m.index 133=(buffers r s (r+s) T).free
  indices : m.index 136=256
  dual : m.index 147=(buffers r s (r+s) T).dual
  dualRank : m.index 148=s
  copyPrimal : m.index 206=(buffers r s (r+s) T).primal
  count : m.index 224=r*(r+s)+s*(r+s)
  dualSource : m.index 225=(buffers r s (r+s) T).primal+r*(r+s)
  dualTarget : m.index 200=(buffers r s (r+s) T).dual
  dualCount : m.index 220=s*(r+s)
  zero : m.index 215=0
  payload : m.index 55=0
  payloadLen : m.index 56=r*(r+s)+s*(r+s)
  address : m.index 57=0
  addressLen : m.index 58=3
  capacity : m.index 60=r*(r+s)+s*(r+s)+4

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem geometryHeaders_correct (C E r s : Nat) (xs : List K) {P : K → Prop}
    (hs : ((start [r,s] xs).memory).AllData P) :
    let m := (start [r,s] xs).memory
    ∃ u k, Block.Eval (Memory.AllData P) (geometryHeaders C E) m k u ∧
      k ≤ (geometryHeaderTime C E).eval (r+s) ∧ u.data=m.data ∧ GeometryHeader r s (polyBound C E (r+s)) u := by
  let m := (start [r,s] xs).memory
  let dims (i : Fin 2) := if i=0 then r else s
  have matchDims (i : Fin 2) : m.index i=dims i := by fin_cases i <;> rfl
  have time : (packetTimeTerm C E).value dims=polyBound C E (r+s) := by
    simp [packetTimeTerm,AddressTerm.value,AddressOp.value,dims,polyBound]
  obtain ⟨h,v,first,hk,fd,fi,value⟩ := (packetTimeTerm C E).correct dims 226 m (by decide) matchDims hs
  have v0 : v.index 0=r := fi 0 (by decide)
  have v1 : v.index 1=s := fi 1 (by decide)
  have vtime := value.trans time
  let env (i : Fin 227) := v.index i
  obtain ⟨u,k,second,hk',fd',low⟩ := HeaderPlan.correct matrixPlan 227 le_rfl v env (fun _ => rfl) first.safe_end
  have initial (i : Nat) : m.index i ≤ r+s := by
    cases i with
    | zero => exact Nat.le_add_right _ _
    | succ i =>
      cases i with
      | zero => exact Nat.le_add_left _ _
      | succ i => exact Nat.zero_le _
  have envBound (i : Fin 227) : env i ≤ r+s+polyBound C E (r+s) := by
    by_cases high : i.val=226
    · change v.index i.val ≤ _
      rw [high,vtime];omega
    · change v.index i.val ≤ _
      rw [fi _ (by have := i.isLt;omega)]
      exact (initial _).trans (Nat.le_add_right ..)
  have dimBound (i : Fin 2) : dims i ≤ r+s := by fin_cases i <;> simp [dims]
  have head : GeometryHeader (v.index 0) (v.index 1) (v.index 226) u :=
    ⟨low 0,low 1,low 2,low 129,low 130,low 131,low 132,low 133,low 136,low 147,low 148,
     low 206,low 224,low 225,low 200,low 220,low 215,low 55,low 56,low 57,low 58,low 60⟩
  refine ⟨u,h+k,first.seq second,?_,fd'.trans fd,?_⟩
  · have h₁ := hk.trans ((packetTimeTerm C E).cost_le dims (r+s) dimBound)
    have h₂ := hk'.trans (HeaderPlan.cost_le matrixPlan env _ envBound)
    simpa only [geometryHeaderTime,eval_add,eval_comp,eval_X,eval_mul,eval_C,eval_pow,eval_one,polyBound]
      using Nat.add_le_add h₁ h₂
  · simpa only [v0,v1,vtime] using head

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
