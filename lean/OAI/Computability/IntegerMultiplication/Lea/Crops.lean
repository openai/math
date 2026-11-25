import OAI.Computability.IntegerMultiplication.Dune.Gate

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Lea
open Code Bits Dune Cap Finset
variable (p:ℕ)
abbrev radix:= (2:ℕ)^p
variable {k:ℕ}
def parcel (x:Fin k→Word) := (List.ofFn x).flatten
abbrev Capacity (p:ℕ)(x:Fin k→Word):Prop:=∀i,(x i).length=p
theorem roundtrip (x:Fin k→Word)(h:Capacity p x): value (parcel x)=score (radix p) (value ∘ x) := by
  induction k with
  | zero=> simp [score,parcel]
  | succ k ih=>
    let v:= fun (i:Fin k)=>x i.succ
    change value (List.ofFn _).flatten=∑ i:Fin (k+1), _
    rw [List.ofFn_succ,List.flatten_cons,value_append,h,Fin.sum_univ_succ,show (0:Fin (k+1)).val=0 from rfl,pow_zero,one_mul]
    rw [show (List.ofFn v).flatten=parcel v from rfl,ih v (fun _=>h _)]
    change _= value (x 0) + ∑ i:Fin k,(radix p)^(i.val+1)*value (v i)
    simp_rw [pow_succ']
    unfold score
    rw [mul_sum]
    simp only [Function.comp_apply]; unfold radix
    congr 1
    exact sum_congr rfl (fun i _=>by ring)

theorem dimension (x:Fin k→Word)(h:Capacity p x) : (parcel x).length=k*p := by
  induction k with
  | zero=>simp [parcel]
  | succ k ih=>
    unfold parcel; rw [List.ofFn_succ,List.flatten_cons,List.length_append,h]
    let v:=fun i:Fin k=> x i.succ
    rw [show (List.ofFn v).flatten=parcel v from rfl,ih v (fun _=>h _)]
    rw [Nat.add_mul]; omega

-- coefficient existence by chopping
private theorem ice (x: Word) (u : x.length=k*p):
    ∃ f:Fin k→Word, Capacity p f ∧ parcel f=x := by
  induction k generalizing x with
  | zero=> refine ⟨Fin.elim0,fun j=>j.elim0,by simpa [parcel] using List.length_eq_zero_iff.mp (by simpa using u) |>.symm⟩
  | succ k ih=>
    have v:p≤x.length:=by rw [u,Nat.add_mul];omega
    let y:=x.drop p
    obtain ⟨f,t,q⟩:=ih y (by unfold y; simp; rw [u,Nat.add_mul]; omega)
    refine ⟨Fin.cons (x.take p) f,?_ ,?_⟩
    · intro i
      exact Fin.cases (by simp [v]) (fun i=>by simpa using t i) i
    unfold parcel; rw [List.ofFn_succ]
    simp_rw [Fin.cons_zero,Fin.cons_succ]; rw [List.flatten_cons, show (List.ofFn f).flatten= parcel f from rfl,q]
    exact List.take_append_drop _ x
variable (k)
noncomputable def crop (x:Word) :Fin k→Word:= Classical.choose (ice p (sized (k*p) x) (sized_length ..))
theorem crop_ (x:Word):
    Capacity p (crop p k x) ∧ parcel (crop p k x)=sized (k*p) x :=
  Classical.choose_spec (ice p (sized (k*p) x) (sized_length ..))
theorem scoreV (x:Word)(e:x.length≤ k*p):
    score (radix p) (value ∘ crop p k x)=value x:= by
  have t: value x<2^(k*p):=(value_lt x).trans_le (Nat.pow_le_pow_right (by decide) e)
  rw [← roundtrip _ _ (crop_ ..).1,(crop_ ..).2,sized_low,Nat.mod_eq_of_lt t]
theorem emptyCrop (x:Word)(v:ℕ)(e:x.length≤ p*v)(g:x.length≤ k*p) (i:Fin k)(h:v ≤ i.val):
    value (crop p k x i)=0:= by
  let f:= value ∘ crop p k x
  have u:= Finset.single_le_sum (f:=fun j:Fin k=> (radix p)^j.val*f j) (s:=univ)
    (fun j _=>Nat.zero_le _) (mem_univ i)
  change _≤ score (radix p) f at u; unfold f at u; rw [scoreV _ _ _ g] at u
  by_contra! W
  have V : 1≤ value (crop p k x i):=Nat.pos_of_ne_zero W
  have C : 2^x.length ≤ (radix p)^i.val := by unfold radix; rw [← pow_mul]; gcongr; first | decide | exact e.trans (Nat.mul_le_mul_left p h)
  exact Nat.not_lt_of_ge (le_trans C ((Nat.le_mul_of_pos_right _ V).trans u)) (value_lt x)

-- obtain chunk directly from tape
def saw (x: (List Tally × Tally) × Word):List Word :=
  (Piecework.segment x.1.1 (resize (x.1.2,x.2))).1
@[fun_prop] theorem sawE: Easy saw := by
  unfold saw
  let f :(List Tally × Tally) × Word→List Tally × Word:=fun x=> (x.1.1,resize (x.1.2,x.2))
  exact ((show Easy f from by unfold f; fun_prop).compose Piecework.easy).fstCompose

theorem sawn (x:Word):
    saw ((List.replicate k (Code.tally p),Code.tally (k*p)),x)=List.ofFn (crop p k x) := by
  unfold saw
  change (Piecework.segment _ (sized (k*p) x)).1=_
  rw [← (crop_ p k x).2,show List.replicate k (Code.tally p)=(List.ofFn (crop p k x)).map (Code.tally ∘ List.length) by
    rw [List.map_ofFn]
    simp only [Function.comp_def,(crop_ p k x).1]
    -- List.ofFn const
    apply List.ext_getElem (by simp); intro; simp]
  rw [parcel,Piecework.prescribed]
end Lea

end IntegerMultiplication
end Computability
end OAI
