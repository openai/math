import OAI.Optimization.LinearProgramming.Compression.SymbolicAddressLoops
import OAI.Optimization.LinearProgramming.Compression.SymbolicAreas
import Mathlib.Tactic.Linarith

/-! Physical initialization of the six persistent workspace pointers. The existing
caller supplies the first free address in register 97. Registers 70–72 are counters. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable

private def linearHeader (dest displacement stride : ℕ) : Block :=
  .seq (copyIndexPlus dest 97 displacement) (addAddressLoop dest 70 83 stride)

private def initializeAddressStart : Block :=
  .straight [.addrCopy 68 97,.addrCopy 88 97,.incr 71 83]

def symbolicWorkspaceBlock : Block :=
  .seq initializeAddressStart <| .seq (linearHeader 69 1 1) <| .seq (linearHeader 87 2 2) <|
  .seq (linearHeader 89 7 4) <| .seq (copyIndexPlus 90 97 9) addSymbolicTokenSpan

def symbolicWorkspaceSteps (n fuel : ℕ) := 16*n+34+(n+1)*(7*fuel+15)

theorem symbolicWorkspaceSteps_le_poly (n fuel : ℕ) :
    symbolicWorkspaceSteps n fuel ≤ polyBound 80 2 (n+fuel) := by
  let s := n+fuel+1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hn : n+1 ≤ s := by dsimp [s]; omega
  have hf : 7*fuel+15 ≤ 22*s := by dsimp [s]; omega
  have hp := Nat.mul_le_mul hn hf
  have hs2 : s ≤ s^2 := Nat.le_self_pow (by decide) s
  change 16*n+34+(n+1)*(7*fuel+15) ≤ 80*s^2
  nlinarith

structure SymbolicWorkspaceAt {K : Type*} (m t : Memory K) (n fuel floor : ℕ) : Prop where
  data : t.data=m.data
  bases : t.index 68=floor
  exponents : t.index 69=floor+(n+1)
  scalarTape : t.index 87=floor+2*(n+1)
  dimSlot : t.index 88=floor
  digits : t.index 89=floor+2*(n+1)+2*n+5
  tokens : t.index 90=floor+9+2*symbolicTokenBudget (n+1) (2*fuel+3)
  kept : ∀ i, (i < 68 ∨ 72 < i) → (i < 87 ∨ 90 < i) → t.index i=m.index i

private def firstState {K : Type*} (m : Memory K) : Memory K :=
  ((m.putIndex 68 (m.index 97)).putIndex 88 (m.index 97)).putIndex 71 (m.index 83+1)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

private theorem linearHeader_eval (m : Memory K) (dst dis stride : ℕ) (hm : m.AllData P)
    (hw : dst ≠ 70) (hc : 83 ≠ dst) :
    ∃ t, Block.Eval (Memory.AllData P) (linearHeader dst dis stride) m
      ((1+dis)+(m.index 83*(stride+3)+2)) t ∧ t.data=m.data ∧
      t.index dst=m.index 97+dis+m.index 83*stride ∧
      ∀ i, i ≠ dst → i ≠ 70 → t.index i=m.index i := by
  let a := m.putIndex dst (m.index 97+dis)
  have start := copyIndexPlus_spec m dst 97 dis hm
  obtain ⟨t,run,post⟩ := addAddressLoop_eval a dst 70 83 stride (show a.AllData P from hm) hw hc (by decide)
  have a83 : a.index 83=m.index 83 := Memory.putIndex_ne _ hc _
  rw [a83] at run
  refine ⟨t,start.seq run,post.data,?_,fun i hd hw' => (post.frame i hd hw').trans (Memory.putIndex_ne _ hd _)⟩
  rw [post.value,a83]
  simp [a]

private theorem first_eval (m : Memory K) (hm : m.AllData P) :
    Block.Eval (Memory.AllData P) initializeAddressStart m 3 (firstState m) := by
  let a := m.putIndex 68 (m.index 97)
  let b := a.putIndex 88 (m.index 97)
  have e₁ := Block.Eval.op_addrCopy (safe:=Memory.AllData P) m 68 97 hm hm
  have e₂ := Block.Eval.op_addrCopy (safe:=Memory.AllData P) a 88 97 hm hm
  have e₃ := Block.Eval.op_incr (safe:=Memory.AllData P) b 71 83 hm hm
  rw [show a.index 97=m.index 97 by simp [a]] at e₂
  rw [show b.index 83=m.index 83 by simp [b,a]] at e₃
  exact e₁.seq (e₂.seq (e₃.seq (.skip hm)))

theorem symbolicWorkspaceBlock_eval (m : Memory K) (n fuel floor : ℕ) (hm : m.AllData P)
    (hn : m.index 83=n) (hf : m.index 84=fuel) (start : m.index 97=floor) :
    ∃ t, Block.Eval (Memory.AllData P) symbolicWorkspaceBlock m (symbolicWorkspaceSteps n fuel) t ∧
      SymbolicWorkspaceAt m t n fuel floor := by
  let a := firstState m
  have head := first_eval m hm
  have a83 : a.index 83=n := by simp [a,firstState,hn]
  have a97 : a.index 97=floor := by simp [a,firstState,start]
  obtain ⟨b,r₁,bd,bv,bf⟩ := linearHeader_eval a 69 1 1 head.safe_end (by decide) (by decide)
  have b83 := (bf 83 (by decide) (by decide)).trans a83
  have b97 := (bf 97 (by decide) (by decide)).trans a97
  obtain ⟨c,r₂,cd,cv,cf⟩ := linearHeader_eval b 87 2 2 r₁.safe_end (by decide) (by decide)
  have c83 := (cf 83 (by decide) (by decide)).trans b83
  have c97 := (cf 97 (by decide) (by decide)).trans b97
  obtain ⟨d,r₃,dd,dv,df⟩ := linearHeader_eval c 89 7 4 r₂.safe_end (by decide) (by decide)
  let e := d.putIndex 90 (d.index 97+9)
  have e97 := (df 97 (by decide) (by decide)).trans c97
  have r₄ := copyIndexPlus_spec d 90 97 9 r₃.safe_end
  obtain ⟨t,r₅,td,tv,tf⟩ := addSymbolicTokenSpan_eval e (show e.AllData P from r₄.safe_end)
  have e71 : e.index 71=n+1 := by
    simp (disch := decide) only [e,Memory.putIndex_ne,df,cf,bf,a,firstState,Memory.putIndex_same,hn]
  have e84 : e.index 84=fuel := by
    simp (disch := decide) only [e,Memory.putIndex_ne,df,cf,bf,a,firstState,hf]
  rw [a83] at r₁
  rw [b83] at r₂
  rw [c83] at r₃
  rw [e71,e84] at r₅
  refine ⟨t,?_,td.trans (dd.trans (cd.trans bd)),?_,?_,?_,?_,?_,?_,?_⟩
  · have clock : 3 + ((2 + (n*4+2)) + ((3 + (n*5+2)) +
          ((8 + (n*7+2)) + (10 + ((n+1)*(7*fuel+15)+2))))) = symbolicWorkspaceSteps n fuel := by
      unfold symbolicWorkspaceSteps
      ring
    rw [← clock]
    exact head.seq (r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅))))
  · simp (disch := decide) only [tf,e,Memory.putIndex_ne,df,cf,bf,a,firstState,Memory.putIndex_same,start]
  · rw [tf 69 (by decide) (by decide) (by decide)]
    simp (disch := decide) only [e,Memory.putIndex_ne,df,cf,bv,a83,a97]
    omega
  · rw [tf 87 (by decide) (by decide) (by decide)]
    simp (disch := decide) only [e,Memory.putIndex_ne,df,cv,b97,b83]
    omega
  · simp (disch := decide) only [tf,e,Memory.putIndex_ne,df,cf,bf,a,firstState,Memory.putIndex_same,start]
  · rw [tf 89 (by decide) (by decide) (by decide)]
    simp (disch := decide) only [e,Memory.putIndex_ne,dv,c83,c97]
    omega
  · rw [tv,e71,e84]
    simp only [e,Memory.putIndex_same,e97,symbolicTokenBudget]
    ring
  · intro i low high
    rw [tf i (by omega) (by omega) (by omega)]
    change (d.putIndex 90 _).index i=m.index i
    rw [Memory.putIndex_ne _ (by omega),df i (by omega) (by omega),cf i (by omega) (by omega),
      bf i (by omega) (by omega)]
    simp [a,firstState,show i ≠ 68 by omega,show i ≠ 88 by omega,show i ≠ 71 by omega]

end Compression
end LinearProgramming
end Optimization
end OAI
