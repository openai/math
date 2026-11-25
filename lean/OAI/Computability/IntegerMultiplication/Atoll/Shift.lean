import OAI.Computability.IntegerMultiplication.Atoll.Gramme
import OAI.Computability.IntegerMultiplication.Cap.Inverse

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Cap Echo Finset
variable {n m:ℕ}
-- natural width m≥n; localized rotate bins.
def slide (e:n ≤ m) (a:ℕ)(x:Fin m): Fin m :=
  if h:x.val<n then glue e (⟨(x.val+a)%n,Nat.mod_lt _ (by omega)⟩) else x
theorem slid_lt (e:n ≤ m)(a)(x:Fin m):
    (slide e a x).val<n ↔ x.val<n := by
  unfold slide; split
  next h=> exact iff_of_true (Echo.validGlue ..) h
  rfl
theorem slid_add (e:n ≤ m)(a b:ℕ)(x:Fin m):
    slide e a (slide e b x)=slide e (a+b) x:=by
  by_cases h:x.val<n
  · have g:= (slid_lt e b x).mpr h
    apply Fin.ext
    unfold slide
    simp only [glue,dite_eq_left h] at *
    simp only [dite_eq_left (Nat.mod_lt (x.val+b) (by omega : 0<n))]
    rw [Nat.mod_add_mod]; congr 1; omega
  simp only [slide,dite_eq_right h]

def debt (n a:ℕ):=n - a%n
theorem slidD(e:n ≤ m)(a)(x:Fin m): slide e (debt n a+a) x=x:=by
  unfold slide
  split
  next h=>
    have p:=Nat.mod_lt a (y:=n) (by omega : 0<n)
    apply Fin.ext
    change (x.val+(debt n a+a))%n=x.val
    rw [Nat.add_mod]
    have u:(debt n a+a)%n=0:= by
      rw [show debt n a+a=a+debt n a from Nat.add_comm ..,← Nat.mod_add_mod]
      unfold debt
      rw [Nat.add_sub_cancel' (Nat.le_of_lt p),Nat.mod_self]
    rw [u]
    simp [Nat.mod_eq_of_lt h]
  rfl

def bank (e:n ≤ m)(a:ℕ): Equiv.Perm (Fin m) where
  toFun := slide e a
  invFun := slide e (debt n a)
  left_inv x:=by rw [slid_add,slidD]
  right_inv x:=by rw [slid_add,add_comm,slidD]

variable {d:ℕ}{r t:Bounds d} (e:r≤t)
-- evaluate from wide positions
def leanValue (r:Bounds d) (i:Fin d)(x:Vector_ t):=
  coefficient r i * ∑ j:Fin d,if j < i then (x j).val*base r j else 0
theorem leanV (x:Vector_ r) (i) : leanValue r i (patch e x)=tilt x i:=rfl
theorem constantV (x y:Vector_ t) (i:Fin d)
    (h:∀ j,j < i → x j=y j): leanValue r i x=leanValue r i y := by
  unfold leanValue; congr 1
  apply sum_congr rfl; intro j _; split
  · rw [h j (by assumption)]
  rfl

def column (u:Bool)(i:Fin d)(x:Vector_ t): Vector_ t:=
  let v:=bank (e i) (leanValue r i x)
  let a:=x i
  Function.update x i (bif u then v a else v.symm a)
theorem column_getF (i:Fin d)(x:Vector_ t):
    column e true i x i=bank (e i) (leanValue r i x) (x i):=
  Function.update_self ..
theorem column_getB (i:Fin d)(x:Vector_ t):
    column e false i x i=(bank (e i) (leanValue r i x)).symm (x i):=
  Function.update_self ..
theorem column_off(u i)(x:Vector_ t){j:Fin d}(h:j≠i):
    column e u i x j=x j:= Function.update_of_ne h ..
theorem constantW (u i x) :
    leanValue r i (column e u i x)=leanValue r i x:=
  constantV _ _ _ (fun _j h=>column_off e u i x (Fin.ne_of_lt h))
def bridgeT (i:Fin d): Equiv.Perm (Vector_ t) where
  toFun:=column e true i
  invFun:=column e false i
  left_inv x:= by
    funext j; by_cases h:j=i
    · subst j; rw [column_getB,column_getF,constantW]; simp
    rw [column_off e _ _ _ h,column_off e _ _ _ h]
  right_inv x:=by
    funext j; by_cases h:j=i
    · subst j; rw [column_getF,column_getB,constantW];simp
    rw [column_off e _ _ _ h,column_off e _ _ _ h]

theorem imageT (h:Nice r)(x:Vector_ r) (l: List (Fin d))
    (S:l.Pairwise (fun i j=>i.val<j.val)): ∀ i,
    l.foldr (fun j v=>column e true j v) (patch e x) i =
      (if i∈l then glue (e i) (turn h x i) else patch e x i) := by
  induction l with
  | nil=>simp
  | cons j l ih=>
    obtain ⟨t,u⟩:=List.pairwise_cons.mp S
    let y:=(List.foldr (fun j v=>column e true j v) (patch e x) l)
    intro i
    change column e true j y i=_
    by_cases p:i=j
    · subst j; rw [column_getF]
      have g : i ∉ l := fun e=>Nat.lt_irrefl _ (t _ e)
      have w:=ih u
      change ∀ i,y i= _ at w
      have W:= constantV (r:=r) y (patch e x) i (by
        intro k v; rw [w k]
        apply ite_eq_right
        exact fun e=>Nat.not_lt_of_ge v.le (t _ e))
      rw [W,leanV,w i,ite_eq_right g,ite_eq_left List.mem_cons_self]
      apply Fin.ext

      change (slide (e i) (tilt x i) (glue (e i) (x i))).val=_
      simp [slide,turn,glue]
    rw [column_off e _ _ _ p] -- replace
    simpa only [List.mem_cons,p,false_or] using ih u i

end Atoll

end IntegerMultiplication
end Computability
end OAI
