import OAI.Computability.IntegerMultiplication.Echo.Stability

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Echo
open Finset Cap IntegerMultiplication.Fourier
variable {d:ℕ} {n:Bounds d}
abbrev Grid_ (X:Type) := Vector_ n→X
abbrev alter (a:Vector_ n) (i:Fin d) (z:Spot (n i)) :Vector_ n:= Function.update a i z
def street {X Y:Type} (i:Fin d) (K: (Spot (n i)→X)→Spot (n i)→Y) (v:Grid_ (n:=n) X):Grid_ (n:=n) Y :=
  fun x=> K (fun z=>v (alter x i z)) (x i)

variable (k:Square n)
noncomputable def profile (l:List (Fin d)) : Square n :=
  fun i=> if i ∈ l then k i else fun x y=>if x=y then 1 else 0

theorem deltaProd (x y:Vector_ n) :
    ∏ i,(if x i=y i then (1:ℂ) else 0) =
    if x=y then 1 else 0 := by
  classical
  split
  · next p=> subst y; simp
  · next p =>
    obtain ⟨i,t⟩ : ∃ i,x i≠y i := not_forall.mp (fun h=>p (funext h))
    apply prod_eq_zero (mem_univ i); rw [ite_eq_right t]

@[simp] theorem erased (v:Along n) :
    strand n (profile k []) v = v := by
  classical
  funext x
  unfold strand profile
  simp only [List.not_mem_nil,↓reduceIte]
  simp_rw [deltaProd]
  simp

private theorem catches (i:Fin d) (l:List (Fin d)) (u:i∉l)
    (x y:Vector_ n) (z:Spot (n i)):
    ∏ j,profile k l j (alter x i z j) (y j)=
    let C:ℂ:=∏ j∈(univ.erase i),profile k l j (x j) (y j)
    (if z=y i then 1 else 0) *C := by
  classical
  dsimp only
  rw [← Finset.mul_prod_erase _ _ (mem_univ i)]
  simp only [alter,Function.update_self,profile,ite_eq_right u]
  congr 1
  apply prod_congr rfl; intro j h
  rw [Function.update_of_ne (mem_erase.mp h).1]
theorem crossing (i:Fin d)(l:List (Fin d)) (u:i∉l) (v:Along n) :
    strand n (profile k (i::l)) v=
      street i (page (k i)) (strand n (profile k l) v) := by
  classical
  funext x
  unfold strand street page
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro y hy
  simp_rw [catches k i l u]
  rw [Finset.sum_eq_single (y i),ite_eq_left rfl,one_mul]
  · rw [← mul_assoc]
    congr 1
    rw [← mul_prod_erase _ _ (mem_univ i)]
    congr 1
    · simp [profile]
    apply prod_congr rfl; intro a h
    have e := (mem_erase.mp h).1
    simp [profile,e]
  · intro b _ e; simp [e]
  simp

theorem schedule (l: List (Fin d)) (v:Along n)
    (p : l.Nodup) (t:∀i,i∈l) :
    l.foldr (fun i x=> street i (page (k i)) x) v=strand n k v := by
  classical
  suffices h : ∀ l:List (Fin d),l.Nodup→ l.foldr (fun i x=> street i (page (k i)) x) v=strand n (profile k l) v from by
    have e : profile k l=k := by funext; simp [profile,t]
    exact (h l p).trans (by rw [e])
  intro l p
  induction l with
  | nil=> simp
  | cons i l ih=>
    have u:=List.nodup_cons.mp p
    simp only [List.foldr_cons]; rw [ih u.2,crossing ..]; exact u.1
end Echo

end IntegerMultiplication
end Computability
end OAI
