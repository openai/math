import OAI.Optimization.LinearProgramming.RAM.RAMIndex
import OAI.Optimization.LinearProgramming.PrimalDual.JointDatum

/-! Compile the signed data selection for a word of the joint feasibility instance. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Tape

open Block
open OAI.Optimization.LinearProgramming.PrimalDual

inductive DatumTerm (n : Nat) where
  | zero | negOne
  | word (offset : AddressTerm n) (negate : Bool)
  | lt (left right : AddressTerm n) (yes no : DatumTerm n)
  deriving Repr

namespace DatumTerm

variable {n : Nat}

def value (v : Fin n → Nat) : DatumTerm n → JointDatum
  | .zero => .zero
  | .negOne => .negOne
  | .word e neg => .source (e.value v) neg
  | .lt l r yes no => if l.value v < r.value v then yes.value v else no.value v

/-- Scalar registers zero and one hold a temporary value and the constant zero. -/
def code (src : Fin n) (a : Nat) : DatumTerm n → Block
  | .zero => .op (.const 0 0)
  | .negOne => .op (.const 0 (-1))
  | .word e neg => .seq ((AddressTerm.reg src + e).code a)
      (.seq (.op (.load 0 a)) (if neg then .op (.sub 0 1 0) else .skip))
  | .lt l r yes no => .seq (l.code a) (.seq (r.code (a+1))
      (.branch (.addrLT a (a+1)) (code src a yes) (code src a no)))

def cost (v : Fin n → Nat) (src : Fin n) : DatumTerm n → Nat
  | .zero | .negOne => 1
  | .word e _ => (AddressTerm.reg src + e).cost v + 2
  | .lt l r yes no => l.cost v + (r.cost v + (2 + max (cost v src yes) (cost v src no)))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem good_write (m : Memory K) (h : Good P m) (i : Nat) (q : K) (hq : P q) :
    Good P (m.putData i q) := by
  intro j
  by_cases hj : j = i
  · simpa [Memory.putData, hj] using hq
  · simpa [Memory.putData, hj] using h j

private theorem eval_constD (m : Memory K) (hm : Good P m) (v : ℚ) (hv : P (v : K)) :
    Eval (Good P) (.op (.const 0 v)) m 1 (m.putData 0 (v : K)) :=
  .op hm (good_write _ hm _ _ hv) (fun _ => rfl)

private theorem eval_loadD (m : Memory K) (hm : Good P m) (loc : Nat) :
    Eval (Good P) (.op (.load 0 loc)) m 1 (m.putData 0 (m.data (m.index loc))) :=
  .op hm (good_write _ hm _ _ (hm _)) (fun _ => rfl)

private theorem eval_negD (m : Memory K) (hm : Good P m) (hz : m.data 1 = 0)
    (hneg : ∀ q, P q → P (-q)) :
    Eval (Good P) (.op (.sub 0 1 0)) m 1 (m.putData 0 (-m.data 0)) := by
  apply Eval.op hm (good_write _ hm _ _ (hneg _ (hm 0)))
  intro pc
  simp [execInstr, Memory.atPC, State.putData, Memory.putData, hz]

/-- Evaluation is validated on the real RAM and changes only scalar register zero.
The address registers below `a` are preserved. -/
theorem correct (e : DatumTerm n) (src : Fin n) (env : Fin n → Nat) (a : Nat) (m : Memory K)
    (hbase : n ≤ a) (henv : ∀ i : Fin n, m.index i = env i) (hs : Good P m)
    (h0 : P 0) (h1 : P (-1)) (hneg : ∀ q, P q → P (-q)) (hz : m.data 1 = 0) :
    ∃ k t, Eval (Good P) (e.code src a) m k t ∧ k ≤ e.cost env src ∧
      (∀ j, j ≠ 0 → t.data j = m.data j) ∧ (∀ i < a, t.index i = m.index i) ∧
      t.data 0 = (e.value env).read (fun j => m.data (env src + j)) := by
  induction e generalizing m with
  | zero =>
    refine ⟨_,_,eval_constD m hs 0 (by simpa using h0),le_rfl,
      fun j hj => Function.update_of_ne hj _ _,fun _ _ => rfl,?_⟩
    simp [Memory.putData, value, JointDatum.read]
  | negOne =>
    refine ⟨_,_,eval_constD m hs (-1) (by simpa using h1),le_rfl,
      fun j hj => Function.update_of_ne hj _ _,fun _ _ => rfl,?_⟩
    simp [Memory.putData, value, JointDatum.read]
  | word e neg =>
    obtain ⟨k,s,hk,hbound,hd,hf,hv⟩ := ((AddressTerm.reg src)+e).correct env a m hbase henv hs
    change s.index a = env src + e.value env at hv
    let t := s.putData 0 (s.data (s.index a))
    have hread := eval_loadD s hk.safe_end a
    cases neg with
    | false =>
      refine ⟨_,t,.seq hk (.seq hread (.skip hread.safe_end)), by change k + (1+0) ≤ _+2; omega,
        fun j hj => (Function.update_of_ne hj _ _).trans (congrFun hd j),hf,?_⟩
      simp [t, Memory.putData, hd, hv, value, JointDatum.read]
    | true =>
      have hz' : t.data 1 = 0 := by simp [t,Memory.putData,hd,hz]
      refine ⟨_,_,.seq hk (.seq hread (eval_negD t hread.safe_end hz' hneg)),
        by change k+(1+1) ≤ _+2; omega, ?_,hf,?_⟩
      · intro j hj
        exact (Function.update_of_ne hj _ _).trans ((Function.update_of_ne hj _ _).trans (congrFun hd j))
      · simp [t, Memory.putData, hd, hv, value, JointDatum.read]
  | lt x y yes no ihY ihN =>
    obtain ⟨kx,s,hex,hkx,hds,hfs,hvx⟩ := x.correct env a m hbase henv hs
    obtain ⟨ky,t,hey,hky,hdt,hft,hvy⟩ := y.correct env (a+1) s (by omega)
      (fun i => (hfs i (i.isLt.trans_le hbase)).trans (henv i)) hex.safe_end
    have hdat : t.data = m.data := hdt.trans hds
    have hfront (i : Nat) (hi : i < a) : t.index i = m.index i :=
      (hft i (by omega)).trans (hfs i hi)
    have he : ∀ i : Fin n, t.index i = env i := fun i =>
      (hfront _ (i.isLt.trans_le hbase)).trans (henv i)
    have hleft := (hft a (by omega)).trans hvx
    have hz' : t.data 1 = 0 := hdat ▸ hz
    by_cases hh : x.value env < y.value env
    · obtain ⟨k,z,hb,hk,hf,hi,hv⟩ := ihY t he hey.safe_end hz'
      have hcond : (Cond.addrLT a (a+1)).test t = true := by simp [Cond.test,hleft,hvy,hh]
      refine ⟨_,z,.seq hex (.seq hey (.branchTrue hcond hb)), ?_,
        fun j hj => (hf j hj).trans (congrFun hdat j),fun i h => (hi i h).trans (hfront i h),?_⟩
      · change kx + (ky + (1+k+1)) ≤ _ + (_ + (2+max _ _))
        omega
      · simpa [value,hh,hdat] using hv
    · obtain ⟨k,z,hb,hk,hf,hi,hv⟩ := ihN t he hey.safe_end hz'
      have hcond : (Cond.addrLT a (a+1)).test t = false := by simp [Cond.test,hleft,hvy,hh]
      refine ⟨_,z,.seq hex (.seq hey (.branchFalse hcond hb)), ?_,
        fun j hj => (hf j hj).trans (congrFun hdat j),fun i h => (hi i h).trans (hfront i h),?_⟩
      · change kx + (ky + (1+k)) ≤ _ + (_ + (2+max _ _))
        omega
      · simpa [value,hh,hdat] using hv

end DatumTerm
end Tape
end RAM
end LinearProgramming
end Optimization
end OAI
