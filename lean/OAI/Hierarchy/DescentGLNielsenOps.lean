import OAI.Hierarchy.DescentGLFiber
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

namespace OAI
/-! # The fixed coordinate XOR instructions used by the binary basis permutation -/

noncomputable section
namespace Hierarchy.DescentGLNielsen
open DescentGL
open scoped BigOperators Classical
variable {m : ℕ}

@[local simp] private theorem zero_ne_succ (i : Fin m) : (0 : Fin (m+1))≠i.succ :=
  Ne.symm (Fin.succ_ne_zero i)

structure Gate (m : ℕ) where
  target : Fin m
  source : Fin m
  apart : target≠source
  deriving DecidableEq

abbrev Instruction (m : ℕ) := Gate m × Bool

def applyGate (g : Gate m) (on : Bool) (x : Bits m) (i : Fin m) : ZMod 2 :=
  if i=g.target ∧ on then x i+x g.source else x i

theorem gate_involution (g : Gate m) (on : Bool) (x : Bits m) : applyGate g on (applyGate g on x)=x := by
  funext i
  by_cases eqn : i=g.target ∧ on
  · simp [applyGate,eqn,Ne.symm g.apart,add_assoc,CharTwo.add_self_eq_zero]
  · simp [applyGate,eqn]

def gateEquiv (g : Gate m) (on : Bool) : Layout m where
  toFun := applyGate g on
  invFun := applyGate g on
  left_inv := gate_involution g on
  right_inv := gate_involution g on
  map_add' := by
    intro a b;funext i
    by_cases eqn : i=g.target ∧ on <;> simp [applyGate,eqn]; abel
  map_smul' := by
    intro s a;funext i
    by_cases eqn : i=g.target ∧ on <;> simp [applyGate,eqn,mul_add,smul_eq_mul]

def applyList : List (Instruction m)→Bits m→Bits m
  | [],x=>x
  | a::g,x=>applyList g (applyGate a.1 a.2 x)

def layout : List (Instruction m)→Layout m
  | []=>LinearEquiv.refl _ _
  | a::g=>(gateEquiv a.1 a.2).trans (layout g)

@[simp] theorem layout_apply (g : List (Instruction m)) (x : Bits m) : layout g x=applyList g x := by
  induction g generalizing x with | nil=>rfl | cons a g ih=>exact ih _

theorem apply_append (a b : List (Instruction m)) (x : Bits m) :
    applyList (a++b) x=applyList b (applyList a x) := by
  induction a generalizing x with | nil=>rfl | cons a as ih=>exact ih _

theorem undo (ops : List (Instruction m)) (x : Bits m) : applyList ops.reverse (applyList ops x)=x := by
  induction ops generalizing x with
  | nil=>rfl
  | cons a ops ih=>simp only [List.reverse_cons,apply_append,applyList,ih,gate_involution]

def raised (g : Gate m) : Gate (m+1) := ⟨g.target.succ,g.source.succ,fun h=>g.apart (Fin.succ_injective _ h)⟩
def raise (q : Instruction m) : Instruction (m+1) := (raised q.1,q.2)

theorem raise_apply (g : Gate m) (b : Bool) (x : Bits (m+1)) :
    applyGate (raised g) b x=Fin.cons (x 0) (applyGate g b (Fin.tail x)) := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i <;> simp [raised,applyGate,Fin.tail]

theorem raised_apply (s : List (Instruction m)) (v : ZMod 2) (x : Bits m) :
    applyList (s.map raise) (Fin.cons v x)=Fin.cons v (applyList s x) := by
  induction s generalizing x with
  | nil=>rfl
  | cons a s ih=>simp only [List.map_cons,applyList,raise,raise_apply,Fin.cons_zero,Fin.tail_cons,ih]

def intoHead (i : Fin m) : Gate (m+1) := ⟨0,i.succ,Ne.symm i.succ_ne_zero⟩
def fromHead (i : Fin m) : Gate (m+1) := ⟨i.succ,0,i.succ_ne_zero⟩

def pins (g : Fin m→Gate (m+1)) (c : Bits m) (slots : List (Fin m)) :=
  slots.map (fun i=>(g i,decide (c i≠0)))

private theorem only_bit (a : ZMod 2) (h : a≠0) : a=1 := (show ∀z : ZMod 2,z≠0→z=1 by decide) a h

theorem into_eval (c : Bits m) (slots : List (Fin m)) (x : Bits (m+1)) :
    applyList (pins intoHead c slots) x =
      Fin.cons (x 0+(slots.map (fun j=>c j*x j.succ)).sum) (Fin.tail x) := by
  induction slots generalizing x with
  | nil =>
    funext i
    refine Fin.cases ?_ (fun j=>?_) i <;> simp [pins,applyList,Fin.tail]
  | cons t slots ih =>
    change applyList (pins intoHead c slots) (applyGate (intoHead t) (decide (c t≠0)) x)=_
    rw [ih]
    have tail : ∀j : Fin m, applyGate (intoHead t) (decide (c t≠0)) x j.succ=x j.succ :=
      fun j=>by simp [applyGate,intoHead]
    have pivot : applyGate (intoHead t) (decide (c t≠0)) x 0=x 0+c t*x t.succ := by
      by_cases z : c t=0
      · simp [z,applyGate,intoHead]
      · simp [applyGate,intoHead,only_bit _ z]
    have tails : Fin.tail (applyGate (intoHead t) (decide (c t≠0)) x)=Fin.tail x := funext tail
    simp only [tails,tail,pivot,List.map_cons,List.sum_cons,add_assoc]

theorem out_head (c : Bits m) (slots : List (Fin m)) (x : Bits (m+1)) :
    applyList (pins fromHead c slots) x 0=x 0 := by
  induction slots generalizing x with
  | nil=>rfl
  | cons t slots ih=>
    change applyList (pins fromHead c slots) (applyGate (fromHead t) _ x) 0=_
    rw [ih];simp [applyGate,fromHead]

theorem out_tail (c : Bits m) (slots : List (Fin m)) (unique : slots.Nodup) (x : Bits (m+1)) (i : Fin m) :
    applyList (pins fromHead c slots) x i.succ=x i.succ+(if i∈slots then c i*x 0 else 0) := by
  induction slots generalizing x with
  | nil=>simp [applyList,pins]
  | cons t slots ih=>
    obtain ⟨fresh,nodup⟩ := List.nodup_cons.mp unique
    change applyList (pins fromHead c slots) (applyGate (fromHead t) (decide (c t≠0)) x) i.succ=_
    rw [ih nodup]
    by_cases same : i=t
    · subst t
      by_cases zero : c i=0
      · simp [fresh,applyGate,fromHead,zero]
      · simp [fresh,applyGate,fromHead,only_bit _ zero]
    · simp [same,applyGate,fromHead]

def headPlan (c : Bits m) := pins intoHead c (List.finRange m)
def tailPlan (c : Bits m) := pins fromHead c (List.finRange m)

theorem head_plan (c : Bits m) (x : Bits (m+1)) :
    applyList (headPlan c) x = Fin.cons (x 0+∑j,c j*x j.succ) (Fin.tail x) := by
  rw [headPlan,into_eval,←List.ofFn_eq_map,Fin.sum_ofFn]

theorem tail_plan (c : Bits m) (x : Bits (m+1)) :
    applyList (tailPlan c) x = Fin.cons (x 0) (fun i=>x i.succ+c i*x 0) := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact out_head ..
  · simpa [tailPlan] using out_tail c (List.finRange m) (List.nodup_finRange _) x j

end Hierarchy.DescentGLNielsen

end
end OAI
