import OAI.Hierarchy.DescentWalshInteger
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # Signed Walsh butterflies on the physical Boolean address coordinates -/
namespace Hierarchy.DescentWalshPhysical
open DescentWalshTables
open scoped BigOperators

abbrev Cube (m : ℕ) := Fin m→Bool

def layer {R : Type*} [AddGroup R] {m : ℕ} (t : Fin m) (x : Cube m→R) (p : Cube m) :=
  if p t then x (Function.update p t false)-x (Function.update p t true)
  else x (Function.update p t false)+x (Function.update p t true)

def steps {R : Type*} [AddGroup R] {m : ℕ} (ts : List (Fin m)) (x : Cube m→R) :=
  ts.foldl (fun f t=>layer t f) x

def transform {R : Type*} [AddGroup R] {m : ℕ} (x : Cube m→R) :=
  steps (List.finRange m).reverse x

def numerator {R : Type*} [Ring R] {m : ℕ} (x : Cube m→R) :=
  transform (fun a=>transform x a * transform x a)

private theorem slice_layer {R : Type*} [AddGroup R] {m : ℕ} (t : Fin m)
    (x : Cube (m+1)→R) (b : Bool) :
    (fun p=>layer t.succ x (Fin.cons b p))=layer t (fun p=>x (Fin.cons b p)) := by
  funext p
  simp only [layer,Fin.cons_succ,←Fin.cons_update]

private theorem slices {R : Type*} [AddGroup R] {m : ℕ} (ts : List (Fin m))
    (x : Cube (m+1)→R) (b : Bool) :
    (fun p=>steps (ts.map Fin.succ) x (Fin.cons b p))=steps ts (fun p=>x (Fin.cons b p)) := by
  induction ts generalizing x with
  | nil=>rfl
  | cons t ts ih=>
    change (fun p=>steps (ts.map Fin.succ) (layer t.succ x) (Fin.cons b p))=
      steps ts (layer t (fun p=>x (Fin.cons b p)))
    rw [ih,slice_layer]

theorem transform_cons {R : Type*} [AddGroup R] {m : ℕ} (x : Cube (m+1)→R)
    (b : Bool) (p : Cube m) :
    transform x (Fin.cons b p)=
      if b then transform (fun q=>x (Fin.cons false q)) p-transform (fun q=>x (Fin.cons true q)) p
      else transform (fun q=>x (Fin.cons false q)) p+transform (fun q=>x (Fin.cons true q)) p := by
  let ts:=(List.finRange m).reverse
  have head : transform x=layer (0 : Fin (m+1)) (steps (ts.map Fin.succ) x) := by
    simp only [transform,steps,ts,List.finRange_succ,List.reverse_cons,←List.map_reverse,List.foldl_append]; rfl
  have low:=congrFun (slices ts x false) p
  have high:=congrFun (slices ts x true) p
  rw [head]
  simp only [layer,Fin.cons_zero,Fin.update_cons_zero]
  change (if b then _-_ else _+_)=_
  rw [show steps (ts.map Fin.succ) x (Fin.cons false p)=_ from low,
    show steps (ts.map Fin.succ) x (Fin.cons true p)=_ from high]; rfl

/-- The all-zero frequency reads the sum of the input after the first pass. -/
theorem transform_zero {R : Type*} [AddCommGroup R] {m : ℕ} (x : Cube m→R) :
    transform x (fun _=>false)=∑p,x p := by
  induction m with
  | zero=>
    have same : (Finset.univ : Finset (Cube 0))={(fun _=>false)} := by
      ext p
      simp only [Finset.mem_univ,Finset.mem_singleton,true_iff]
      exact Subsingleton.elim _ _
    rw [same,Finset.sum_singleton]
    rfl
  | succ m ih=>
    let q : Cube m:=fun _=>false
    have split : (fun _ : Fin (m+1)=>false)=Fin.cons false q := by
      funext i
      refine Fin.cases ?_ (fun j=>?_) i <;> rfl
    rw [split,transform_cons]
    simp only [Bool.false_eq_true,ite_false]
    rw [show transform (fun u=>x (Fin.cons false u)) q=_ from ih _,
      show transform (fun u=>x (Fin.cons true u)) q=_ from ih _]
    rw [←(Fin.consEquiv (fun _ : Fin (m+1)=>Bool)).sum_comp x,Fintype.sum_prod_type,Fintype.sum_bool]
    first | rfl | exact add_comm _ _

private def tag (z : ZMod 2) : Bool := decide (z≠0)
private def untag (b : Bool) : ZMod 2 := if b then 1 else 0

def coordinates (m : ℕ) : Bits m≃Cube m where
  toFun a i:=tag (a i)
  invFun a i:=untag (a i)
  left_inv a:=funext fun i=>(show ∀z : ZMod 2,untag (tag z)=z from by decide) (a i)
  right_inv a:=funext fun i=>(show ∀b : Bool,tag (untag b)=b from by decide) (a i)

theorem coordinates_add {m : ℕ} (a b : Bits m) :
    coordinates m (a+b)=fun i=>(coordinates m a i).xor (coordinates m b i) := by
  funext i
  exact (show ∀u v : ZMod 2,tag (u+v)=(tag u).xor (tag v) from by decide) (a i) (b i)

private theorem untag_cons {m : ℕ} (b : Bool) (p : Cube m) :
    (coordinates (m+1)).symm (Fin.cons b p)=Fin.cons (untag b) ((coordinates m).symm p) := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [coordinates,Equiv.coe_fn_symm_mk,Fin.cons_zero]
  · simp only [coordinates,Equiv.coe_fn_symm_mk,Fin.cons_succ]

private def eval {R : Type*} {m : ℕ} (t : Table R m) (p : Cube m) := t.read ((coordinates m).symm p)

private theorem eval_branch {R : Type*} {m : ℕ} (a b : Table R m) (j : Bool) (p : Cube m) :
    eval (.branch a b) (Fin.cons j p)=if j then eval b p else eval a p := by
  simp only [eval,untag_cons,Table.read,Fin.cons_zero,Fin.tail_cons]
  cases j <;> simp [untag]

private theorem eval_combine {R : Type*} {m : ℕ} (op : R→R→R) (a b : Table R m) (p : Cube m) :
    eval (Table.combine op a b).1 p=op (eval a p) (eval b p) := Table.combine_read ..

private theorem transform_table {R : Type*} [AddGroup R] {m : ℕ} (t : Table R m) :
    transform (eval t)=eval t.transform.1 := by
  induction t with
  | scalar a=>rfl
  | @branch n a b ha hb=>
    have lo : (fun q=>eval (.branch a b) (Fin.cons false q))=eval a := by
      funext q; simp only [eval_branch,Bool.false_eq_true,ite_false]
    have hi : (fun q=>eval (.branch a b) (Fin.cons true q))=eval b := by
      funext q; simp only [eval_branch,ite_true]
    have read (j : Bool) (q : Cube n) :
        transform (eval (.branch a b)) (Fin.cons j q)=eval (Table.transform (.branch a b)).1 (Fin.cons j q) := by
      rw [transform_cons,lo,hi,ha,hb]
      cases j <;> simp only [Table.transform,eval_branch,Bool.false_eq_true,ite_false,ite_true,eval_combine]
    funext p
    simpa only [Fin.cons_self_tail] using read (p 0) (Fin.tail p)

/-- The two physical passes yield the ordinary XOR autocorrelation multiplied
by the exact number of Boolean addresses. -/
theorem numerator_exact {m : ℕ} (x : Cube m→ℤ) (d : Cube m) :
    numerator x d=2^m*(∑a : Cube m,x a*x (fun i=>(a i).xor (d i))) := by
  classical
  let t:=Table.tabulate m (fun a=>x (coordinates m a))
  have read : eval t=x := by
    funext a
    simp only [t,eval,Table.tabulate_read,Equiv.apply_symm_apply]
  have square : (fun a=>transform x a*transform x a)=eval (Table.combine (·*·) t.transform.1 t.transform.1).1 := by
    rw [←read,transform_table]
    funext a
    exact (eval_combine _ _ _ _).symm
  rw [numerator,square,transform_table]
  change (integerNumerator t).1.read ((coordinates m).symm d)=_
  rw [integerNumerator_exact,←(coordinates m).sum_comp (fun a=>x a*x (fun i=>(a i).xor (d i)))]
  simp only [t,Table.tabulate_read,coordinates_add,Equiv.apply_symm_apply]

end Hierarchy.DescentWalshPhysical

end OAI
