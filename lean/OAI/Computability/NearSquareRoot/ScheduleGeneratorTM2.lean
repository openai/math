import Mathlib.Computability.TuringMachine.StackTuringMachine
import OAI.Computability.IntegerMultiplication.SM.Output

/-!
# Compiling effectively generated candidates onto P192 tapes

Mathlib's TM2 semantics evaluates a finite expression of stack instructions per
step. Here every push, pop, read, branch and jump is a separate P192 stack-machine
step. A finite set of supported Mathlib labels gives a finite physical control
by retaining only the subexpressions occurring at those labels.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorTM2
open IntegerMultiplication Turing Function
variable {A K Λ σ : Type}

abbrev Stmt (A K Λ σ : Type) := TM2.Stmt (fun _ : K => A) Λ σ
abbrev Source (A K Λ σ : Type) := TM2.Cfg (fun _ : K => A) Λ σ

variable (M : Λ → Stmt A K Λ σ) (S : Finset Λ)

abbrev Site := {q : Option (Stmt A K Λ σ) // q ∈ TM2.stmts M S}

abbrev PC := Site M S × σ

private noncomputable def ptr (q : Option (Stmt A K Λ σ)) : Site M S := by
  classical
  exact if h : q ∈ TM2.stmts M S then ⟨q,h⟩ else ⟨none,by simp [TM2.stmts]⟩

private theorem ptr_val {q : Option (Stmt A K Λ σ)} (h : q ∈ TM2.stmts M S) :
    (ptr M S q).val = q := by simp [ptr,h]

private def atSite (q : Site M S) (v : σ) (r : K → List A) : SM.Config A (PC M S) K :=
  ⟨(q,v),r⟩

noncomputable def cfg (x : Source A K Λ σ) : SM.Config A (PC M S) K :=
  atSite M S (ptr M S (x.l.map M)) x.var x.stk

variable [DecidableEq K]

private def modify (i : K) (a : SM.Action A) : K → SM.Action A :=
  Function.update (fun _ => .skip) i a

/-- Each local variable is part of finite control. All action operands are obtained
from that state and under-head symbols of the stacks. -/
noncomputable def compile : SM.Rule A (PC M S) K := fun (l,v) heads =>
  let go (q : Option (Stmt A K Λ σ)) (w : σ) (acts : K → SM.Action A) :=
    some ((ptr M S q,w),acts)
  match l.val with
  | none => none
  | some code =>
    match code with
    | .push i f q => go q v (modify i (.push (f v)))
    | .peek i f q => go q (f v (heads i)) (fun _ => .skip)
    | .pop i f q => go q (f v (heads i)) (modify i .pop)
    | .load f q => go q (f v) (fun _ => .skip)
    | .branch f q q' => go (if f v then q else q') v (fun _ => .skip)
    | .goto f => go (M (f v)) v (fun _ => .skip)
    | .halt => go none v (fun _ => .skip)

private theorem perform_modify (i : K) (a : SM.Action A) (r : K → List A) :
    (fun k => (modify i a k).perform (r k)) = Function.update r i (a.perform (r i)) := by
  funext k
  by_cases h : k = i <;> simp [modify,Function.update_apply,h,SM.Action.perform]

private theorem one (q : Stmt A K Λ σ) (v : σ) (r : K → List A)
    (hq : some q ∈ TM2.stmts M S) (q' : Option (Stmt A K Λ σ)) (v' : σ)
    (a : K → SM.Action A) (r' : K → List A)
    (step : compile M S (⟨some q,hq⟩,v) (fun k => (r k).head?) = some ((ptr M S q',v'),a))
    (hr : (fun k => (a k).perform (r k)) = r') :
    SM.advance (compile M S) (atSite M S (ptr M S (some q)) v r) =
      some (atSite M S (ptr M S q') v' r') := by
  have hh : ptr M S (some q) = ⟨some q,hq⟩ := Subtype.ext (ptr_val M S hq)
  rw [hh]
  unfold SM.advance
  change (compile M S (⟨some q,hq⟩,v) _).map _ = _
  rw [show SM.tops (atSite M S ⟨some q,hq⟩ v r) = (fun k => (r k).head?) from rfl,step]
  exact congrArg some (congrArg (SM.Config.mk (ptr M S q',v')) hr)

/-- Execute one entire finite TM2 expression, accounting for every instruction. -/
theorem runAux (q : Stmt A K Λ σ) (hq : some q ∈ TM2.stmts M S) (v : σ) (r : K → List A) :
    ∃ t, Trace (SM.advance (compile M S)) (atSite M S (ptr M S (some q)) v r) t
      (cfg M S (TM2.stepAux q v r)) := by
  classical
  induction q generalizing v r with
  | push i f q ih =>
    have hq' := TM2.stmts_trans (q₁ := q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) hq
    obtain ⟨t,tr⟩ := ih hq' v (Function.update r i (f v :: r i))
    exact ⟨_,Trace.cons (one M S _ v r hq _ _ _ _ rfl (perform_modify _ _ _)) tr⟩
  | peek i f q ih =>
    have hq' := TM2.stmts_trans (q₁ := q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) hq
    obtain ⟨t,tr⟩ := ih hq' (f v (r i).head?) r
    exact ⟨_,Trace.cons (one M S _ v r hq _ _ _ _ rfl rfl) tr⟩
  | pop i f q ih =>
    have hq' := TM2.stmts_trans (q₁ := q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) hq
    obtain ⟨t,tr⟩ := ih hq' (f v (r i).head?) (Function.update r i (r i).tail)
    exact ⟨_,Trace.cons (one M S _ v r hq _ _ _ _ rfl (perform_modify _ _ _)) tr⟩
  | load f q ih =>
    have hq' := TM2.stmts_trans (q₁ := q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) hq
    obtain ⟨t,tr⟩ := ih hq' (f v) r
    exact ⟨_,Trace.cons (one M S _ v r hq _ _ _ _ rfl rfl) tr⟩
  | branch f p q ihp ihq =>
    have h₁ := TM2.stmts_trans (q₁ := p) (by simp [TM2.stmts₁,TM2.stmts₁_self]) hq
    have h₂ := TM2.stmts_trans (q₁ := q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) hq
    cases hv : f v with
    | false =>
      obtain ⟨t,tr⟩ := ihq h₂ v r
      simp only [TM2.stepAux,hv,Bool.cond_false]
      exact ⟨_,Trace.cons (one M S _ v r hq (some q) v (fun _ => .skip) r (by simp [compile,hv]) rfl) tr⟩
    | true =>
      obtain ⟨t,tr⟩ := ihp h₁ v r
      simp only [TM2.stepAux,hv,Bool.cond_true]
      exact ⟨_,Trace.cons (one M S _ v r hq (some p) v (fun _ => .skip) r (by simp [compile,hv]) rfl) tr⟩
  | goto f => exact ⟨1,Trace.single (one M S _ v r hq _ _ _ _ rfl rfl)⟩
  | halt => exact ⟨1,Trace.single (one M S _ v r hq _ _ _ _ rfl rfl)⟩

omit [DecidableEq K] in
private theorem mem_root {l : Λ} (h : l ∈ S) : some (M l) ∈ TM2.stmts M S := by
  classical
  simp only [TM2.stmts,Finset.some_mem_insertNone,Finset.mem_biUnion]
  exact ⟨l,h,TM2.stmts₁_self⟩

/-- A finitely supported TM2 run yields an ordinary finite P192 stack trace. -/
theorem run [Inhabited Λ] (support : TM2.Supports M S) {x y : Source A K Λ σ}
    (hx : x.l ∈ Finset.insertNone S) (reach : StateTransition.Reaches (TM2.step M) x y) :
    ∃ t, Trace (SM.advance (compile M S)) (cfg M S x) t (cfg M S y) := by
  obtain ⟨_,t,hr⟩ : y.l ∈ Finset.insertNone S ∧ ∃ t,
      Trace (SM.advance (compile M S)) (cfg M S x) t (cfg M S y) := by
    induction reach with
    | refl => exact ⟨hx,0,.nil _⟩
    | @tail u y _ step ih =>
      obtain ⟨hu,n,tr⟩ := ih
      refine ⟨TM2.step_supports M support step hu,?_⟩
      obtain ⟨label,v,r⟩ := u
      cases label with
      | none => simp [TM2.step] at step
      | some label =>
        have hl : label ∈ S := Finset.some_mem_insertNone.mp hu
        have hstep : y = TM2.stepAux (M label) v r := by simpa [TM2.step] using step.symm
        subst y
        obtain ⟨k,tail⟩ := runAux M S (M label) (mem_root M S hl) v r
        exact ⟨_,tr.trans tail⟩
  exact ⟨t,hr⟩

theorem halt (v : σ) (r : K → List A) :
    SM.advance (compile M S) (cfg M S (TM2.Cfg.mk none v r)) = none := by
  unfold SM.advance
  simp [cfg,atSite,compile,ptr,TM2.stmts]

end GeneratorTM2

end NearSquareRoot
end Computability
end OAI
