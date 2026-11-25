import OAI.Computability.IntegerMultiplication.Atoll.Gramme

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Wave
open Strip Dims Loom Cap Atoll
variable {A B C:Type}
private theorem prod_get (l:List A)(q:List B)(i j:ℕ)(h:i<l.length)(v:j<q.length):
    (l.product q)[i*q.length+j]'(by rw [show (l.product q).length=l.length*q.length from List.length_product _ _]; nlinarith [Nat.mul_le_mul_right q.length h])=(l[i],q[j]) := by
  have aux (l : List A) (i : ℕ) (hi : i < l.length) :
      (l.product q)[i*q.length+j]? = some (l[i],q[j]) := by
    induction l generalizing i with
    | nil => simp at hi
    | cons a l ih =>
      cases i with
      | zero =>
        simp only [Nat.zero_mul, Nat.zero_add]
        change (q.map (fun y => (a,y)) ++ l.product q)[j]? = _
        rw [List.getElem?_append_left (by simpa using v)]
        simp [v]
      | succ i =>
        change (q.map (fun y => (a,y)) ++ l.product q)[(i+1)*q.length+j]? = _
        rw [List.getElem?_append_right (by simp only [List.length_map, Nat.succ_mul]; omega)]
        simp only [List.length_map, List.getElem_cons_succ]
        have heq : (i+1)*q.length+j-q.length = i*q.length+j := by rw [Nat.succ_mul]; omega
        rw [heq]
        exact ih i (Nat.lt_of_succ_lt_succ hi)
  have e := aux l i h
  rw [List.getElem?_eq_getElem (by rw [show (l.product q).length=l.length*q.length from List.length_product _ _]; nlinarith [Nat.mul_le_mul_right q.length h])] at e
  exact Option.some.inj e

theorem cart_rank (s:Series A)(t:Series B) (a:A)(b:B):
    ((s.cart t).index (a,b)).val=(s.index a).val*t.count+(t.index b).val := by
  let n:=s.index a
  let m:=t.index b
  let q:=s.cart t
  have h:n.val<s.explore.length:=n.isLt
  have v:m.val<t.explore.length:=m.isLt
  have W:= prod_get _ _ _ _ h v
  let u:=n.val*t.count+m.val
  have p: u<q.count:=by
    rw [Series.count_cart]; change _< s.explore.length*t.explore.length
    unfold u; change n.val*t.explore.length+m.val<_; nlinarith [Nat.mul_le_mul_right t.explore.length h]
  have E : q.follow ⟨u,p⟩=(a,b):= by
    change (s.explore.product t.explore)[_]'_=(a,b)
    exact W.trans (Prod.ext (s.follow_index _) (t.follow_index _))
  have z:= congrArg Fin.val (show q.index (a,b)=⟨u,p⟩ by rw [← E,q.index_follow])
  exact z

theorem adoption (s:Series A)(t:Series B)(c:Adopt s t) (a:A):
    (s.index a).val=(t.index (c.cast a)).val := by
  let f : Fin t.count := t.index (c.cast a)
  obtain ⟨m,v⟩:=f
  -- better get equality at s index a in route
  let j:=s.index a
  let k:=t.index (c.cast a)
  let w:Fin t.count:=⟨j.val,by rw [← c.cost]; exact j.isLt⟩
  have e: (t.tab t.index)[w.val]'(by rw [Series.card]; exact w.isLt)=k := by
    simp only [c.route (t.index)]
    rw [s.get _ j]
    unfold j; simp [k]
  rw [t.get _ w] at e
  rw [Equiv.apply_symm_apply] at e
  exact congrArg Fin.val e

theorem rank_ (s:Series A)(t:Series B)(c:Adopt s t) (a:B):
    (s.index (c.cast.symm a)).val=(t.index a).val:= by
  simpa only [Equiv.apply_symm_apply] using adoption _ _ c (c.cast.symm a)
theorem natural_rank {n:ℕ} (i:Fin n):
    ((Series.natural n).index i).val=i.val := by
  let s:=Series.natural n
  have j:s.follow ⟨i.val,by simp [s]⟩=i := Series.get_natural ..
  exact congrArg Fin.val (show s.index i= _ by rw [← j,Series.index_follow])
end Wave

end IntegerMultiplication
end Computability
end OAI
