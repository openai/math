import OAI.Computability.BorderVNP.CubeISAOwnedTrace

/-! # Chronological private words of the owned-row scanner

This version records every callback's actual private bits. Rejected digit
candidates fall through without consuming a bit. The native counter, fixed
preparation, and branch guards are included in the tick bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Owned

open VPVNP.BurstRAM DiagonalResidueRAM Finset

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Raw physical state after advancing a word-sized cursor using its unit register. -/
def bumpBank (s : Bank w) (cursor : Reg) : Bank w :=
  Function.update s cursor (s cursor + s 1)

private theorem bump_run (cursor : Reg) (s : Bank w) (m : Memory w) :
    TraceRun pub mac (.binary .add cursor cursor 1) s m [] 1 (fun t mt => t = bumpBank s cursor ∧ mt = m) := by
  have r : Runs pub mac (.binary .add cursor cursor 1) s m [tick w] (bumpBank s cursor) m :=
    Runs.localStep m rfl rfl
  exact ⟨_,_,_,r,by simp [TraceOK,tick],le_rfl,rfl,rfl⟩

/-- The chronological concatenation of private bits from the selected row
candidates, as a list indexed by the finite local counter. -/
def rowChoices {N : ℕ} (select : Fin N → Prop) [DecidablePred select] (bs : Fin N → List Bool) :=
  (List.ofFn fun t => if select t then bs t else []).flatten

/-- A full native row for prescribed local private bits. Preparation preserves
the actual word bank invariants needed by the physical scatter callback. -/
theorem traceRow_run {N : ℕ} (candidate body : Code) (prep : ℕ)
    (select : Fin N → Prop) [DecidablePred select] (bs : Fin N → List Bool) (cost : Fin N → ℕ)
    (I : ℕ → Bank w → Memory w → Prop) (P : Fin N → Bank w → Memory w → Prop)
    (regs : ∀ k s m, I k s m → readings s 18 = k ∧ readings s 19 = N)
    (prepare : ∀ (t : Fin N) s m, I t.val s m → TraceRun pub mac candidate s m [] prep (P t))
    (flag : ∀ t s m, P t s m → (s 40 = s 1 ↔ select t))
    (visit : ∀ t, select t → ∀ s m, P t s m → TraceRun pub mac body s m (bs t) (cost t)
      (fun u mu => I (t.val+1) (bumpBank u 18) mu))
    (skip : ∀ t, ¬select t → ∀ s m, P t s m → I (t.val+1) (bumpBank s 18) m)
    (s : Bank w) (m : Memory w) (start : I 0 s m) :
    TraceRun pub mac (rowLoop candidate body) s m (rowChoices select bs)
      ((∑ t : Fin N, (prep+3 + if select t then cost t else 1))+1) (I N) := by
  let b (k : ℕ) := if h : k < N then (if select ⟨k,h⟩ then bs ⟨k,h⟩ else []) else []
  let v (k : ℕ) := if h : k < N then (if select ⟨k,h⟩ then cost ⟨k,h⟩ else 1) else 1
  have step k (hk : k < N) s m (hi : I k s m) :
      TraceRun pub mac (.seq candidate (.seq (.ifEq 40 1 body .nop) (.binary .add 18 18 1))) s m
        (b k) (prep+(1+v k+1)) (I (k+1)) := by
    let t : Fin N := ⟨k,hk⟩
    have selectRun u mu (hu : P t u mu) :
        TraceRun pub mac (.ifEq 40 1 body .nop) u mu (b k) (1+v k)
          (fun a ma => I (k+1) (bumpBank a 18) ma) := by
      apply TraceRun.branch
      by_cases valid : select t
      · have he := (flag t u mu hu).mpr valid
        have ht : select ⟨k,hk⟩ := valid
        simpa [he,b,v,hk,t,ht] using visit t valid u mu hu
      · have he := (flag t u mu hu).not.mpr valid
        have no : Runs pub mac .nop u mu [tick w] u mu := Runs.localStep mu rfl rfl
        have eqn : b k = [] := by simp [b,hk,← show t = ⟨k,hk⟩ from rfl,valid]
        rw [ite_eq_right he,eqn,show v k = 1 by simp [v,hk,← show t = ⟨k,hk⟩ from rfl,valid]]
        exact ⟨_,_,_,no,by simp [TraceOK,tick],le_rfl,skip t valid u mu hu⟩
    have step' := (prepare t s m hi).seq (fun u mu hu =>
      (selectRun u mu hu).seq (fun a ma ha => (bump_run 18 a ma).mono le_rfl
        (fun z mz ⟨hz,hm⟩ => hz ▸ hm ▸ ha)))
    simpa only [List.nil_append,List.append_nil] using step'
  have run := trace_counted 18 19 _ N (fun k => prep+(1+v k+1)) b I regs step 0 (Nat.zero_le _) s m start
  have same : (List.range' 0 (N-0)).flatMap b = rowChoices select bs := by
    simp only [Nat.sub_zero,← List.range_eq_range',rowChoices, List.flatMap_def]
    apply congrArg List.flatten
    apply List.ext_getElem (by simp)
    intro i h _
    have hi : i < N := by simpa using h
    simp [b,hi]
  rw [same] at run
  apply run.mono ?_ (fun _ _ h => h)
  rw [Nat.Ico_zero_eq_range,← Fin.sum_univ_eq_sum_range]
  apply Nat.add_le_add_right
  apply sum_le_sum
  intro t _
  have eqn : v t.val = if select t then cost t else 1 := by
    unfold v; rw [dite_eq_left t.isLt]
  rw [eqn]
  omega

end RoutingISA.Owned

end BorderVNP
end Computability
end OAI
