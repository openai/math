import OAI.Optimization.LinearProgramming.NativePrice.Tape
import OAI.Optimization.LinearProgramming.Lattice.QueryWire

/-! Materialize the two-bit reply of the lattice sign oracle from the native
comparison's literal three-way return tag. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM NativePrice

def comparisonTag : Ordering → ℕ
  | .lt => 0
  | .eq => 1
  | .gt => 2

private def outputPair (x y : Bool) : Block := .straight [
  .const 0 (x.toNat:ℚ), .const 1 (y.toNat:ℚ), .store 47 0,
  .addrCopy 46 47, .incr 46 46, .store 46 1, .addrConst 49 2]

/-- Address 14 holds the numeric comparison tag, 47 is the reply base, and
49 receives the literal length two. Ordinary scalar words at that base
receive the reply, preserving all other high address registers. -/
def signReplyBlock : Block :=
  .seq (.straight [.addrConst 16 1,.addrConst 18 2]) (.branch (.addrLT 14 16)
    (outputPair false false)
    (.branch (.addrLT 14 18) (outputPair false true) (outputPair true false)))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private structure PairPost (u s : Memory K) (base : ℕ) (x y : Bool) : Prop where
  word : WordAt s base [x,y]
  length : s.index 49=2
  frameIndex : ∀ i, i ≠ 46 → i ≠ 49 → s.index i=u.index i
  frameData : ∀ i, 2 ≤ i → i ≠ base → i ≠ base+1 → s.data i=u.data i

private theorem outputPair_spec (P : K → Prop) (u : Memory K) (base : ℕ) (x y : Bool)
    (hu : u.AllData P) (hb : u.index 47=base) (hbase : 2 ≤ base) (h0 : P 0) (h1 : P 1) :
    ∃ s, Block.Eval (Memory.AllData P) (outputPair x y) u 7 s ∧ PairPost u s base x y := by
  let u₁ := u.putData 0 ((x.toNat:ℚ):K)
  let u₂ := u₁.putData 1 ((y.toNat:ℚ):K)
  let u₃ := u₂.putData (u₂.index 47) (u₂.data 0)
  let u₄ := u₃.putIndex 46 (u₃.index 47)
  let u₅ := u₄.putIndex 46 (u₄.index 46+1)
  let u₆ := u₅.putData (u₅.index 46) (u₅.data 1)
  let s := u₆.putIndex 49 2
  have h₁ : u₁.AllData P := hu.putData _ (by cases x <;> simp_all)
  have h₂ : u₂.AllData P := h₁.putData _ (by cases y <;> simp_all)
  have h₃ : u₃.AllData P := h₂.putData _ (h₂ _)
  have h₄ : u₄.AllData P := h₃
  have h₅ : u₅.AllData P := h₄
  have h₆ : u₆.AllData P := h₅.putData _ (h₅ _)
  have hs : s.AllData P := h₆
  have e := (Block.Eval.op_const u 0 (x.toNat:ℚ) hu h₁).seq
    ((Block.Eval.op_const u₁ 1 (y.toNat:ℚ) h₁ h₂).seq
      ((Block.Eval.op_store u₂ 47 0 h₂ h₃).seq ((Block.Eval.op_addrCopy u₃ 46 47 h₃ h₄).seq
        ((Block.Eval.op_incr u₄ 46 46 h₄ h₅).seq ((Block.Eval.op_store u₅ 46 1 h₅ h₆).seq
          ((Block.Eval.op_addrConst u₆ 49 2 h₆ hs).seq (.skip hs)))))))
  refine ⟨s,e,?_,by simp [s],?_,?_⟩
  · apply wordAt_cons.mpr
    constructor
    · simp [s,u₆,u₅,u₄,u₃,u₂,u₁,hb]
    · apply wordAt_cons.mpr
      refine ⟨?_,by simp [WordAt]⟩
      simp [s,u₆,u₅,u₄,u₃,u₂,u₁,hb,show 1 ≠ base by omega]
  · intro i h46 h49
    simp [s,u₆,u₅,u₄,u₃,u₂,u₁,h46,h49]
  · intro i hi hbase' hnext
    simp [s,u₆,u₅,u₄,u₃,u₂,u₁,hb,hbase',hnext,show i ≠ 0 by omega,show i ≠ 1 by omega]

/-- All three orderings, including exact equality, are given their prescribed
two-bit response through actual store instructions. -/
theorem signReplyBlock_spec (P : K → Prop) (o : Ordering) (m : Memory K) (base : ℕ)
    (hm : m.AllData P) (ht : m.index 14=comparisonTag o) (hb : m.index 47=base)
    (hbase : 2 ≤ base) (h0 : P 0) (h1 : P 1) :
    ∃ s k, k ≤ 13 ∧ Block.Eval (Memory.AllData P) signReplyBlock m k s ∧
      WordAt s base (Lattice.signReply o) ∧ s.index 47=base ∧ s.index 49=2 ∧
      (∀ i, i ≠ 16 → i ≠ 18 → i ≠ 46 → i ≠ 49 → s.index i=m.index i) ∧
      (∀ i, 2 ≤ i → i ≠ base → i ≠ base+1 → s.data i=m.data i) := by
  let u := m.putIndex 16 1
  let v := u.putIndex 18 2
  have hu : u.AllData P := hm
  have hv : v.AllData P := hu
  have init := (Block.Eval.op_addrConst m 16 1 hm hu).seq
    ((Block.Eval.op_addrConst u 18 2 hu hv).seq (.skip hv))
  have vb : v.index 47=base := by simpa [v,u] using hb
  have branch (x y : Bool) := outputPair_spec P v base x y hv vb hbase h0 h1
  have final {s : Memory K} {x y : Bool} (h : PairPost v s base x y) :
      s.index 47=base ∧ s.index 49=2 ∧
      (∀ i, i ≠ 16 → i ≠ 18 → i ≠ 46 → i ≠ 49 → s.index i=m.index i) ∧
      (∀ i, 2 ≤ i → i ≠ base → i ≠ base+1 → s.data i=m.data i) := by
    refine ⟨(h.frameIndex _ (by decide) (by decide)).trans vb,h.length,?_,h.frameData⟩
    intro i h16 h18 h46 h49
    simpa [v,u,h16,h18] using h.frameIndex i h46 h49
  cases o with
  | lt =>
    obtain ⟨s,e,h⟩ := branch false false
    have cond : (Cond.addrLT 14 16).test v=true := by simp [Cond.test,v,u,ht,comparisonTag]
    exact ⟨s,11,by decide,init.seq (Block.Eval.branchTrue (k:=7) cond e),h.word,final h⟩
  | eq =>
    obtain ⟨s,e,h⟩ := branch false true
    have c₀ : (Cond.addrLT 14 16).test v=false := by simp [Cond.test,v,u,ht,comparisonTag]
    have c₁ : (Cond.addrLT 14 18).test v=true := by simp [Cond.test,v,u,ht,comparisonTag]
    exact ⟨s,12,by decide,init.seq (Block.Eval.branchFalse (k:=9) c₀ (Block.Eval.branchTrue (k:=7) c₁ e)),h.word,final h⟩
  | gt =>
    obtain ⟨s,e,h⟩ := branch true false
    have c₀ : (Cond.addrLT 14 16).test v=false := by simp [Cond.test,v,u,ht,comparisonTag]
    have c₁ : (Cond.addrLT 14 18).test v=false := by simp [Cond.test,v,u,ht,comparisonTag]
    exact ⟨s,11,by decide,init.seq (Block.Eval.branchFalse (k:=8) c₀ (Block.Eval.branchFalse (k:=7) c₁ e)),h.word,final h⟩

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
