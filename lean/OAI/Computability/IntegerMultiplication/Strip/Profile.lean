import OAI.Computability.IntegerMultiplication.Fix.Expense

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code _root_.OAI.Computability.IntegerMultiplication.Fix
variable {I J O T K B A C X : Type}
def intercept [DecidableEq I] (t : O → I) (i : I) (v : O→X) :=
  fun x:O => if t x = i then [v x] else []
structure File (s : Series O) (I) [DecidableEq I] (t : Series B) where
  focus : Lens O I B
  sees {A : Type} (i : I) (v : O→A) :
    (s.tab (intercept (Prod.fst ∘ ⇑focus) i v)).flatten =
      t.tab (fun b => v (focus.symm (i,b)))
namespace File
variable [DecidableEq I] [DecidableEq J]
variable {s : Series O} {b : Series B} {t : Series T} {c : Series C}
def look (s : Series I) : File s I Series.one where
  focus := (Equiv.prodPUnit _).symm
  sees {_} i v := by
    have h : ∀ l : List I, l.Nodup →
        (l.map (fun x => if x=i then [v x] else [])).flatten = if i∈l then [v i] else [] := by
      intro l u
      induction l with
      | nil => simp
      | cons a l ih =>
        rw [List.nodup_cons] at u
        by_cases e : a=i
        · subst i; simp [ih u.2,u.1]
        simp [ih u.2,e,Ne.symm e]
    change (List.map (fun x:I => if x=i then [v x] else []) _).flatten=[v i]
    rw [h _ s.nodup,ite_eq_left (s.complete _)]

def shade (s : Series O) : File s Unit s where
  focus := (Equiv.punitProd _).symm
  sees {_} i v := by
    change (s.explore.map (fun x => if ()=(i:PUnit) then [v x] else [])).flatten=s.explore.map v
    cases i
    induction s.explore <;> simp_all

private def grids (f : Lens O I B) (g : Lens T J C) :
    Lens (O × T) (I × J) (B × C) where
  toFun x := (((f x.1).1,(g x.2).1),(f x.1).2,(g x.2).2)
  invFun x := (f.symm (x.1.1,x.2.1),g.symm (x.1.2,x.2.2))
  left_inv v := by simp
  right_inv v := by simp

private theorem squash (s : Series A) (f : A→List (List X)) :
    ((s.tab f).flatten).flatten=(s.tab (fun i => (f i).flatten)).flatten := by
  unfold Series.tab
  induction s.explore with
  | nil => rfl
  | cons x l ih => simp [ih,List.flatten_append]

def unite (u : File s I b) (w : File t J c) : File (s.cart t) (I × J) (b.cart c) where
  focus := grids u.focus w.focus
  sees {X} x v := by
    rw [Series.grouped,b.grouped]
    have out (u0 : O) : ((t.tab (fun b : T => intercept
        (Prod.fst ∘ ⇑(grids u.focus w.focus)) x v (u0,b)))).flatten =
        if (u.focus u0).1=x.1 then c.tab (fun a => v (u0,w.focus.symm (x.2,a))) else [] := by
      by_cases e:(u.focus u0).1=x.1
      · rw [ite_eq_left e]
        have d := w.sees x.2 fun b => v (u0,b)
        obtain ⟨x,y⟩ := x
        simp only [grids,Function.comp_def,intercept,Equiv.coe_fn_mk,Prod.mk.injEq,e,true_and]
        exact d
      rw [ite_eq_right e]
      suffices eq : (fun b : T => intercept (Prod.fst ∘ ⇑(grids u.focus w.focus)) x v (u0,b))=fun _=>[] by
        rw [eq]
        unfold Series.tab
        induction t.explore <;> simp_all
      funext b
      unfold intercept grids
      obtain ⟨j,k⟩ := x
      simp [e]
    rw [squash]
    simp only [out]
    -- filtered prefix via treating list c.tab as atom
    let a i := c.tab (fun y => v (i,w.focus.symm (x.2,y)))
    have key : (s.tab (fun i => if (u.focus i).1=x.1 then a i else [])).flatten =
        ((b.tab (fun i => a (u.focus.symm (x.1,i))))).flatten := by
      rw [← u.sees x.1 a,squash]
      congr 2
      ext i
      unfold intercept
      by_cases e:(u.focus i).1=x.1 <;> simp [e]
    rw [key]
    rfl

end File
end Strip

end IntegerMultiplication
end Computability
end OAI
