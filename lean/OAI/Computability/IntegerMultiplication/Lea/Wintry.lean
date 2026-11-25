import OAI.Computability.IntegerMultiplication.Lea.Input

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Lea
open Code Bits Cap Finset
abbrev Rod:=List Tally×Tally
abbrev Trigger:= List Word×Rod
-- peel addresses
def pan (x:Trigger):Word × List Word :=
  ((lock (fun v:Word×Tally=> resize (v.2,v.1)) [] [] (x.1,x.2.1)).flatten,
    lock (fun v:Word×Tally=>(cutLists (v.2,v.1)).2) [] [] (x.1,x.2.1))
@[fun_prop] theorem panE : Easy pan:= by
  have a:Easy (lock (fun v:Word×Tally=>resize (v.2,v.1)) [] []) := easy_lock _ (by fun_prop) _ _
  have b: Easy (lock (fun v:Word×Tally=>(cutLists (v.2,v.1)).2) [] []) := easy_lock _ ((easy_cut Easy.exchange).sndCompose) _ _
  unfold pan; fun_prop

-- global powers of shift evaluation
def harvest : ℕ →Trigger→Word
| 0=>fun _=>[]
| k+1=> fun x=>
  let q:=pan x
  Bits.add (q.1, fill false x.2.2 ++ harvest k (q.2,x.2))
@[fun_prop] theorem harvestE (k:ℕ):Easy (harvest k):= by
  induction k with
  | zero=> exact Easy.const []
  | succ k ih=> unfold harvest; fun_prop

variable {m:ℕ}(p:ℕ)
abbrev scale0(m k:ℕ):Rod:=(List.replicate m (Code.tally k),Code.tally k)
abbrev downP (x:Fin m→Word)(i:Fin m):Word:=(x i).drop p
theorem reap (x:Fin m→Word):
    pan (List.ofFn x,scale0 m p)=(parcel (sized p ∘ x), List.ofFn (downP p x)):= by
  unfold pan parcel
  -- dsimp only
  change ((lock _ [] [] (List.ofFn x, List.replicate m _)).flatten, lock _ [] [] (List.ofFn x,List.replicate m _))=_
  rw [maskLock,maskLock]
  refine Prod.ext rfl ?_
  change List.ofFn _=_
  apply congrArg List.ofFn
  funext i
  simp [cutLists,downP]

private theorem step_u (x:Word):
    value x=value (sized p x) + 2^p*value (x.drop p):= by
  rw [sized_low]
  by_cases h:x.length≤p
  · have P:value x<2^p:= (value_lt x).trans_le (Nat.pow_le_pow_right (by decide) h)
    rw [List.drop_eq_nil_of_le h,value_nil,mul_zero,add_zero,Nat.mod_eq_of_lt P]
  have Q:=value_append (x.take p) (x.drop p)
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by omega)] at Q
  have U:value (x.take p)<2^p:= by convert! value_lt (x.take p); simp;omega
  conv_rhs=> lhs; rw [Q,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt U]
  exact Q

theorem savored (k:ℕ) (x:Fin m→Word)(v:∀ i,(x i).length ≤ k*p):
    value (harvest k (List.ofFn x,scale0 m p))= Cap.score (radix p) (value ∘ x):= by
  induction k generalizing x with
  | zero=>
    have E(i):x i=[]:=List.length_eq_zero_iff.mp (by simpa using v i)
    simp [harvest,E,Cap.score]
  | succ k ih=>
    unfold harvest
    rw [reap]
    change value (Bits.add (_, fill false _ ++ _))=_
    rw [add_val,value_append,fill_eq,Code.tally_length,zeroes,List.length_replicate,zero_add]
    change value (parcel (sized p ∘ x))+2^p*value (harvest k (List.ofFn (downP p x),scale0 m p))=_
    rw [roundtrip p (sized p ∘ x) (fun _=> sized_length ..),ih _]
    · unfold Cap.score radix
      rw [mul_sum,← sum_add_distrib]
      refine sum_congr rfl fun i _=>?_
      dsimp only [Function.comp_apply]
      rw [step_u p (x i)] -- may rewrite in sized argument?
      unfold downP;ring
    intro j
    change ((x j).drop p).length≤_
    rw [List.length_drop]
    specialize v j
    rw [Nat.add_mul] at v; omega
end Lea

end IntegerMultiplication
end Computability
end OAI
