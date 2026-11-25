import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.RAM.Loops
import Mathlib.Tactic.Ring

/-! A counted loop producing a dyadic scalar and its explicit binary digits. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Address 2 is the write cursor and address 3 holds a constructed bit. The first word of
this tape is one. Each loop iteration doubles the scalar and writes another zero bit. -/
private def parameterPowerInit (out counter : ℕ) : Block :=
  .seq (.op (.const out 1)) <| .seq (.op (.const counter 0)) <|
  .seq (.op (.addrConst 3 1)) <| .seq (.op (.addrStore 2 3)) <|
  .seq (.op (.incr 2 2)) (.op (.addrConst 3 0))

private def parameterPowerStep (one out counter : ℕ) : Block :=
  .seq (.op (.add out out out)) <| .seq (.op (.add counter counter one)) <|
  .seq (.op (.addrStore 2 3)) (.op (.incr 2 2))

/-- Compute `2^e` given the natural exponent as a scalar. Scalar `counter` and `out`,
address 2 and 3, and the tape beginning at the entry value of address 2 are writable. -/
def parameterPowerBlock (exponent one out counter : ℕ) : Block :=
  .seq (parameterPowerInit out counter)
    (.loop (.scalarLT counter exponent) (parameterPowerStep one out counter))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private structure PowerInvariant (P : K → Prop) (entry : Memory K) (base out counter j : ℕ)
    (s : Memory K) : Prop where
  safe : s.AllData P
  scalar : s.data out = (2:K)^j
  count : s.data counter = (j:K)
  cursor : s.index 2 = base+j+1
  scratch : s.index 3 = 0
  dataFrame : ∀ i, i≠out → i≠counter → s.data i = entry.data i
  indexFrame : ∀ i, i≠2 → i≠3 → (i < base ∨ base + j < i) → s.index i = entry.index i
  digits : ∀ r ≤ j, s.index (base+r) = if r=0 then 1 else 0

private theorem parameterPowerInit_spec (P : K → Prop) (m : Memory K) (base out counter : ℕ)
    (hs : m.AllData P) (h₀ : P 0) (h₁ : P 1) (hc : counter≠out) (hbase : m.index 2=base)
    (hb : 4 ≤ base) : ∃ s, Block.Eval (Memory.AllData P) (parameterPowerInit out counter) m 6 s ∧
      PowerInvariant P m base out counter 0 s := by
  let m₁ := m.putData out 1
  let m₂ := m₁.putData counter 0
  let m₃ := m₂.putIndex 3 1
  let m₄ := m₃.putIndex base 1
  let m₅ := m₄.putIndex 2 (base+1)
  let m₆ := m₅.putIndex 3 0
  have e₁ : Block.Eval (Memory.AllData P) (.op (.const out 1)) m 1 m₁ := by
    simpa [m₁] using Block.Eval.op_const m out 1 hs (by simpa using hs.putData out h₁)
  have h₁' : m₁.AllData P := hs.putData out h₁
  have h₂ : m₂.AllData P := h₁'.putData counter h₀
  have e₂ : Block.Eval (Memory.AllData P) (.op (.const counter 0)) m₁ 1 m₂ := by
    simpa [m₂] using Block.Eval.op_const m₁ counter 0 h₁' (by simpa using h₂)
  have e₃ := Block.Eval.op_addrConst m₂ 3 1 h₂ h₂
  have cur : m₃.index 2 = base := by simpa [m₃,m₂,m₁,Memory.putIndex] using hbase
  have bit : m₃.index 3 = 1 := by simp [m₃]
  have e₄ : Block.Eval (Memory.AllData P) (.op (.addrStore 2 3)) m₃ 1 m₄ := by
    simpa only [cur,bit] using Block.Eval.op_addrStore m₃ 2 3 h₂ h₂
  have cur' : m₄.index 2 = base := by simpa [m₄,Memory.putIndex,Function.update_of_ne (by omega : 2≠base)] using cur
  have e₅ : Block.Eval (Memory.AllData P) (.op (.incr 2 2)) m₄ 1 m₅ := by
    simpa only [cur'] using Block.Eval.op_incr m₄ 2 2 h₂ h₂
  have e₆ := Block.Eval.op_addrConst (safe := Memory.AllData P) m₅ 3 0 h₂ h₂
  refine ⟨m₆,e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq e₆)))),h₂,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [m₆,m₅,m₄,m₃,m₂,m₁,Memory.putIndex,Memory.putData,Function.update_of_ne hc.symm]
  · simp [m₆,m₅,m₄,m₃,m₂,Memory.putIndex]
  · simp [m₆,m₅,Memory.putIndex]
  · simp [m₆]
  · intro i hi hj; simp [m₆,m₅,m₄,m₃,m₂,m₁,Memory.putIndex,Memory.putData,Function.update_of_ne hi,Function.update_of_ne hj]
  · intro i hi hj hfar
    have hib : i ≠ base := by omega
    simp [m₆,m₅,m₄,m₃,m₂,m₁,Memory.putIndex,Function.update_of_ne hi,Function.update_of_ne hj,Function.update_of_ne hib]
  · intro r hr; obtain rfl : r=0 := by omega
    simp [m₆,m₅,m₄,Memory.putIndex,Function.update_of_ne (by omega : base≠2),Function.update_of_ne (by omega : base≠3)]

private theorem parameterPowerStep_spec (P : K → Prop) (m s : Memory K)
    (base one out counter j : ℕ) (hs : PowerInvariant P m base out counter j s)
    (hb : 4 ≤ base) (hc : counter≠out) (ho : one≠out) (ht : one≠counter)
    (hone : m.data one=1) (hp : P ((2:K)^(j+1))) (hn : P ((j+1:ℕ):K)) :
    ∃ t, Block.Eval (Memory.AllData P) (parameterPowerStep one out counter) s 4 t ∧
      PowerInvariant P m base out counter (j+1) t := by
  let s₁ := s.putData out (s.data out+s.data out)
  let s₂ := s₁.putData counter (s₁.data counter+s₁.data one)
  let s₃ := s₂.putIndex (base+j+1) 0
  let t := s₃.putIndex 2 (base+j+2)
  have hpow : s.data out + s.data out = (2:K)^(j+1) := by rw [hs.scalar,pow_succ]; ring
  have hsafe₁ : s₁.AllData P := hs.safe.putData out (hpow ▸ hp)
  have hsone : s.data one=1 := (hs.dataFrame one ho ht).trans hone
  have hcounter : s₁.data counter + s₁.data one = ((j+1:ℕ):K) := by
    simp [s₁,Memory.putData,Function.update_of_ne hc,Function.update_of_ne ho,hs.count,hsone]
  have hsafe₂ : s₂.AllData P := hsafe₁.putData counter (hcounter ▸ hn)
  have e₁ := Block.Eval.op_add s out out out hs.safe hsafe₁
  have e₂ := Block.Eval.op_add s₁ counter counter one hsafe₁ hsafe₂
  have e₃ : Block.Eval (Memory.AllData P) (.op (.addrStore 2 3)) s₂ 1 s₃ := by
    simpa only [s₃,s₂,s₁,Memory.putData_index,hs.cursor,hs.scratch] using
      Block.Eval.op_addrStore s₂ 2 3 hsafe₂ hsafe₂
  have cur : s₃.index 2=base+j+1 := by
    simpa [s₃,s₂,s₁,Memory.putIndex,Function.update_of_ne (by omega : 2≠base+j+1)] using hs.cursor
  have e₄ : Block.Eval (Memory.AllData P) (.op (.incr 2 2)) s₃ 1 t := by
    simpa only [cur] using Block.Eval.op_incr s₃ 2 2 hsafe₂ hsafe₂
  refine ⟨t,e₁.seq (e₂.seq (e₃.seq e₄)),hsafe₂,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [t,s₃,s₂,s₁,Memory.putIndex,Memory.putData,Function.update_of_ne hc.symm] using hpow
  · simpa [t,s₃,s₂,Memory.putIndex,Memory.putData] using hcounter
  · simp [t, Nat.add_assoc]
  · simpa [t,s₃,s₂,s₁,Memory.putIndex,Function.update_of_ne (by omega : 3≠base+j+1)] using hs.scratch
  · intro i hi hj
    simpa [t,s₃,s₂,s₁,Memory.putIndex,Memory.putData,Function.update_of_ne hi,Function.update_of_ne hj] using hs.dataFrame i hi hj
  · intro i hi hj hfar
    have hne : i≠base+j+1 := by omega
    simpa [t,s₃,s₂,s₁,Memory.putIndex,Function.update_of_ne hi,Function.update_of_ne hne] using
      hs.indexFrame i hi hj (by omega)
  · intro r hr
    have hi : base+r ≠ 2 := by omega
    by_cases hnew : r=j+1
    · subst r
      simp [t,s₃,Memory.putIndex,Function.update_of_ne hi,Nat.add_assoc]
    · have ht' : base+r ≠ base+j+1 := by omega
      simpa [t,s₃,s₂,s₁,Memory.putIndex,Function.update_of_ne hi,Function.update_of_ne ht'] using hs.digits r (by omega)

/-- Exact cost, scalar output, digit tape and preservation outside the selected workspace. -/
theorem parameterPowerBlock_spec (P : K → Prop) (m : Memory K) (base exponent one out counter e : ℕ)
    (hb : 4≤base) (hbase : m.index 2=base) (hexp : m.data exponent=(e:K)) (hone : m.data one=1)
    (hex₁ : exponent≠out) (hex₂ : exponent≠counter) (ho : one≠out) (ht : one≠counter)
    (hc : counter≠out) (hs : m.AllData P) (hp : ∀ j≤e, P ((2:K)^j)) (hn : ∀ j≤e, P (j:K)) :
    ∃ t, Block.Eval (Memory.AllData P) (parameterPowerBlock exponent one out counter) m (6*e+7) t ∧
      t.data out=(2:K)^e ∧ t.data counter=(e:K) ∧ t.index 2=base+e+1 ∧
      (∀ i, i≠out → i≠counter → t.data i=m.data i) ∧
      (∀ i, i≠2 → i≠3 → (i < base ∨ base + e < i) → t.index i=m.index i) ∧
      (∀ r≤e, t.index (base+r)=if r=0 then 1 else 0) := by
  obtain ⟨s,hi,hI⟩ := parameterPowerInit_spec P m base out counter hs (by simpa using hn 0 (Nat.zero_le _))
    (by simpa using hp 0 (Nat.zero_le _)) hc hbase hb
  obtain ⟨t,he,hT⟩ := Block.Eval.loop_invariant_exact
    (c := .scalarLT counter exponent) (body := parameterPowerStep one out counter)
    (PowerInvariant P m base out counter) s e 4 hI
    (fun j hj s h => by
      have he := (h.dataFrame exponent hex₁ hex₂).trans hexp
      refine ⟨by simpa [Cond.test,h.count,he] using hj,?_⟩
      exact parameterPowerStep_spec P m s base one out counter j h hb hc ho ht hone (hp _ hj) (hn _ hj))
    (fun s h => by
      have he := (h.dataFrame exponent hex₁ hex₂).trans hexp
      exact ⟨by simp [Cond.test,h.count,he],h.safe⟩)
  refine ⟨t,?_,hT.scalar,hT.count,hT.cursor,hT.dataFrame,hT.indexFrame,hT.digits⟩
  unfold parameterPowerBlock
  rw [show 6*e+7 = 6+(e*(4+2)+1) by omega]
  exact hi.seq he

end Compression
end LinearProgramming
end Optimization
end OAI
