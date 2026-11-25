import OAI.Optimization.LinearProgramming.Compression.PowerPairPackingRational
import OAI.Optimization.LinearProgramming.Compression.SymbolicAreas

/-! Serialize the selected signed-power operands from the persistent caller's
descriptor registers. The base, exponent, digit and output arrays can be reused
for every comparison of the same size. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

def symbolicPairSetup : Block := Block.straight
  [.addrCopy 2 89, .addrCopy 55 87, .addrCopy 59 90]

def symbolicSerialize : Block :=
  .seq symbolicPairSetup (packPowerPairsBlock scalarExponentTokenBlock)

private def setupMemory (m : Memory ℚ) : Memory ℚ :=
  ((m.putIndex 2 (m.index 89)).putIndex 55 (m.index 87)).putIndex 59 (m.index 90)

private theorem symbolicPairSetup_eval (m : Memory ℚ) {P : ℚ → Prop} (hm : m.AllData P) :
    Block.Eval (Memory.AllData P) symbolicPairSetup m 3 (setupMemory m) := by
  let a := m.putIndex 2 (m.index 89)
  let b := a.putIndex 55 (m.index 87)
  have e₁ := Block.Eval.op_addrCopy (safe := Memory.AllData P) m 2 89 hm hm
  have e₂ := Block.Eval.op_addrCopy (safe := Memory.AllData P) a 55 87 hm hm
  have e₃ := Block.Eval.op_addrCopy (safe := Memory.AllData P) b 59 90 hm hm
  have eq₂ : a.index 87=m.index 87 := by simp [a]
  have eq₃ : b.index 90=m.index 90 := by simp [b,a]
  rw [eq₂] at e₂
  rw [eq₃] at e₃
  exact e₁.seq (e₂.seq (e₃.seq (.skip hm)))

theorem symbolicSerialize_eval (b : SymbolicPairAreas) (N w : ℕ) (ps : List (ℚ×ℤ))
    (m : Memory ℚ) {P : ℚ → Prop} (hm : m.AllData P) (valid : b.Valid N w)
    (hn : ps.length ≤ N) (h50 : m.index 50=ps.length)
    (h51 : m.index 51=b.bases) (h52 : m.index 52=b.exponents)
    (h87 : m.index 87=b.scalarTape) (h89 : m.index 89=b.digits) (h90 : m.index 90=b.tokenStart)
    (reads : ∀ i, ∀ h : i < ps.length, m.data (b.bases+i)=ps[i].1 ∧ m.data (b.exponents+i)=(ps[i].2:ℚ))
    (hw : ∀ x ∈ ps.map Prod.snd, x.natAbs < 2^w)
    (closed : ∀ v : ℕ, v ≤ 2^(2*w+2) → P (v:ℚ)) :
    let es := ps.map Prod.snd
    ∃ t k, k ≤ symbolicEncodeSteps N w ∧ Block.Eval (Memory.AllData P) symbolicSerialize m k t ∧
      PowerPairsReady (ps.map Prod.fst) es b.scalarTape
        (b.tokenStart-(2*(signedBitTape es).length+8)) m t ∧ SymbolicSerializeFrame b N w m t := by
  dsimp only
  let xs := ps.map Prod.fst
  let es := ps.map Prod.snd
  let u := setupMemory m
  have hx : xs.length=ps.length := List.length_map (as := ps) Prod.fst
  have he : es.length=ps.length := List.length_map (as := ps) Prod.snd
  have initialData : u.data=m.data := rfl
  have hu : u.AllData P := hm
  have hzero : P 0 := by simpa using closed 0 (Nat.zero_le _)
  have hone : P 1 := by simpa using closed 1 (Nat.one_le_pow _ _ (by decide))
  have expected : es.length*(w+2) ≤ symbolicTokenBudget N w := by
    rw [he]; exact Nat.mul_le_mul_right _ hn
  have hT := (signedBitTape_length_le es hw).trans expected
  have baseRead (i) (hi : i < xs.length) : u.data (b.bases+i)=xs[i] := by
    rw [initialData]
    simpa [xs] using (reads i (hx ▸ hi)).1
  have expRead (i) (hi : i < es.length) : u.data (b.exponents+i)=(es[i]:ℚ) := by
    rw [initialData]
    simpa [es] using (reads i (he ▸ hi)).2
  obtain ⟨t,k,hk,run,ready,df,af⟩ := packPowerPairsBlock_spec (rationalPowerTokenEmitter closed)
    xs es u b.digits b.bases b.scalarTape b.exponents b.tokenStart hu hzero hone (hx.trans he.symm)
    (by simp [u,setupMemory,h89]) (by simp [u,setupMemory,h50,he])
    (by simp [u,setupMemory,h51]) (by simp [u,setupMemory,h52])
    (by simp [u,setupMemory,h87]) (by simp [u,setupMemory,h90]) (by have := valid.digitsHigh; omega)
    (by have := valid.basesHigh; omega) (by have := valid.scalarHigh; omega)
    (by have := valid.exponentsHigh; omega) (by have := valid.tokenRoom; omega)
    (by have := valid.expDigits; omega) (by have := valid.baseDigits; omega)
    (by have := valid.baseTape; omega) baseRead expRead hw
  have cap : es.length ≤ N := he.le.trans hn
  have cost : 3+k ≤ symbolicEncodeSteps N w := by
    unfold symbolicEncodeSteps
    apply Nat.add_le_add_left
    exact hk.trans (by gcongr)
  have old : u.index 60=m.index 60 := by simp [u,setupMemory]
  have full : PowerPairsReady xs es b.scalarTape (b.tokenStart-(2*(signedBitTape es).length+8)) m t :=
    { ready with oldExtent := ready.oldExtent.trans old }
  refine ⟨t,3+k,cost,(symbolicPairSetup_eval m hm).seq run,full,?_,?_⟩
  · intro i hi h40 h41 digits dest
    have nwords : (powerPairScalarWords xs).length=xs.length+4 := by
      simp only [powerPairScalarWords,List.length_append,List.length_cons,List.length_nil]
      omega
    exact (df i hi h40 h41 digits (by omega)).trans (congrFun initialData i)
  · intro i hi h52' h54 h55 h56 h57 h58 h59 tok
    have e := af i hi h52' h54 h56 h57 h58 (by omega)
    simpa [u,setupMemory,h59,h55,show i ≠ 2 by omega] using e

end Compression
end LinearProgramming
end Optimization
end OAI
