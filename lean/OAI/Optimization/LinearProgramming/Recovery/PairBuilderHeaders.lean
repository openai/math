import OAI.Optimization.LinearProgramming.RAM.FrameHeaders
import OAI.Optimization.LinearProgramming.RAM.RAMFrame
import OAI.Optimization.LinearProgramming.RAM.CallableOddLeaf

/-! Fresh staging headers may read a fixed set of actual registers. Their cost is independent
of old values in all other logical registers, including unrelated hidden solver state. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder

open RAM RAM.Call RAM.Callable RAM.Tape

abbrev Plan := HeaderPlan 220
abbrev Env := Fin 220→ℕ

def reads : AddressTerm 220 → Finset (Fin 220)
  | .val _ => ∅
  | .reg i => {i}
  | .binary _ a b => reads a ∪ reads b

def needed : Plan → Finset (Fin 220)
  | [] => ∅
  | (i,e)::tail => reads e ∪ (needed tail).erase i

def written : Plan → Finset (Fin 220)
  | [] => ∅
  | (i,_)::tail => insert i (written tail)

theorem term_congr (e : AddressTerm 220) (v w : Env) (agree : ∀i∈reads e,v i=w i) :
    e.value v=e.value w ∧ e.cost v=e.cost w := by
  induction e with
  | val => exact ⟨rfl,rfl⟩
  | reg i => exact ⟨agree i (Finset.mem_singleton_self i),rfl⟩
  | binary op a b ia ib =>
    obtain ⟨av,ac⟩ := ia (fun i hi=>agree i (Finset.mem_union_left _ hi))
    obtain ⟨bv,bc⟩ := ib (fun i hi=>agree i (Finset.mem_union_right _ hi))
    exact ⟨by simp only [AddressTerm.value,av,bv], by simp only [AddressTerm.cost,av,ac,bv,bc]⟩

theorem plan_cost_congr (p : Plan) (v w : Env) (agree : ∀i∈needed p,v i=w i) :
    p.cost v=p.cost w := by
  induction p generalizing v w with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨dst,e⟩:=hd
    obtain ⟨valEq,costEq⟩:=term_congr e v w (fun i hi=>agree i (Finset.mem_union_left _ hi))
    have hu : ∀i∈needed tl,Function.update v dst (e.value v) i=Function.update w dst (e.value w) i := by
      intro i hi
      by_cases h : i=dst
      · subst i; simpa using valEq
      · rw [Function.update_of_ne h,Function.update_of_ne h]
        exact agree i (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h,hi⟩))
    simp only [HeaderPlan.cost,costEq,ih _ _ hu]

theorem plan_output_keeps (p : Plan) (v : Env) (i : Fin 220) (hi : i∉written p) : p.output v i=v i := by
  induction p generalizing v with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨dst,e⟩
    simp only [written,Finset.mem_insert,not_or] at hi
    exact (ih _ hi.2).trans (Function.update_of_ne hi.1 _ _)

def header (p : Plan) : Fragment := Odd.leaf (p.code 220)

/-- Exact updates on the public low bank, a frame above the compiler scratch and a
fixed polynomial time bound on just the addresses the macro actually reads. -/
theorem header_run {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (p : Plan) (static : (p.code 220).indexWritesBelow 512=true)
    (e m : Memory K) (P : K→Prop) (he : e.AllData P) (hm : m.AllData P) (bound : ℕ)
    (fits : ∀i∈needed p,m.index i ≤ bound) :
    ∃ t k, (header p).Run P (Odd.memory e m) k (Odd.memory e t) ∧ k ≤ 4*p.budget.eval bound ∧
      t.AllData P ∧ t.data=m.data ∧ (∀i : Fin 220,t.index i=p.output (fun j=>m.index j) i) ∧
      (∀i : Fin 220,i∉written p → t.index i=m.index i) ∧ ∀i,512 ≤ i → t.index i=m.index i := by
  let real : Env := fun i=>m.index i
  let trim : Env := fun i=>if i∈needed p then m.index i else 0
  have hc : p.cost real=p.cost trim := plan_cost_congr p real trim (by intro i hi; simp [real,trim,hi])
  have ht : ∀i,trim i ≤ bound := by
    intro i; by_cases hi : i∈needed p
    · simpa [trim,hi] using fits i hi
    · simp [trim,hi]
  obtain ⟨t,c,run,clock,data,idx⟩:=HeaderPlan.correct p 220 le_rfl m real (fun _=>rfl) hm
  have link := Odd.leaf_run P e he run
  have poly : c ≤ p.budget.eval bound := clock.trans (hc.le.trans (p.cost_le trim bound ht))
  refine ⟨t,4*c,link,Nat.mul_le_mul_left _ poly,
    run.safe_end,data,idx,fun i hi=>(idx i).trans (plan_output_keeps p real i hi),fun i hi=>run.index_frame static hi⟩
end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
