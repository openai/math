import OAI.Hierarchy.DescentHaloWalkRAM
import OAI.Hierarchy.DescentSortedRoster
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

namespace OAI
/-! # The dense ascending roster of genuine old sites reachable in at most ten hops -/
namespace Hierarchy.DescentTenHopRoster
open DescentSortedRoster DescentHaloWalkRAM
noncomputable section
variable {H D : ℕ} (peer : Fin H→Fin D→Option (Fin H))

def follow (digits : List (Fin (D+1))) (start : Option (Fin H)) : Option (Fin H) :=
  digits.foldl (step peer) start

def endpoints (v : Fin H) (p : Fin ((D+1)^10)) : Option (Fin H) :=
  follow peer (List.ofFn (finFunctionFinEquiv.symm p : Fin 10→Fin (D+1))) (some v)

def oldWithin := indexed (endpoints peer)

inductive Walk : ℕ→Fin H→Fin H→Prop where
  | nil (v) : Walk 0 v v
  | cons {n u v z} (edge : ∃i,peer u i=some v) (rest : Walk n v z) : Walk (n+1) u z

def Reach (v z : Fin H) := ∃n≤10,Walk peer n v z

theorem follow_append (xs ys) (v : Option (Fin H)) :
    follow peer (xs++ys) v=follow peer ys (follow peer xs v) := by
  induction xs generalizing v with
  | nil=>rfl
  | cons x xs ih=>exact ih (step peer v x)

theorem follow_none (xs) : follow peer xs none=none := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    change follow peer xs (step peer none x)=none
    have gone : step peer none x=none := by unfold step;split <;> rfl
    rwa [gone]

theorem follow_wait (n : ℕ) (u : Option (Fin H)) :
    follow peer (List.replicate n (Fin.last D)) u=u := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [List.replicate_succ]
    change follow peer (List.replicate n (Fin.last D)) (step peer u (Fin.last D))=u
    simpa only [step,dite_eq_right (show ¬(Fin.last D).val<D from Nat.lt_irrefl D)] using ih

theorem follow_walk {v z : Fin H} (xs) (hit : follow peer xs (some v)=some z) :
    ∃n≤xs.length,Walk peer n v z := by
  induction xs generalizing v with
  | nil=>obtain rfl:=Option.some.inj hit;exact ⟨0,le_rfl,.nil _⟩
  | cons i xs ih=>
    change follow peer xs (step peer (some v) i)=some z at hit
    by_cases live : i.val<D
    · simp only [step,dite_eq_left live,Option.bind_some] at hit
      cases h : peer v ⟨i.val,live⟩ with
      | none=>rw [h,follow_none] at hit;contradiction
      | some u=>
        rw [h] at hit
        obtain ⟨n,le,walk⟩:=ih hit
        exact ⟨n+1,Nat.succ_le_succ le,.cons ⟨_,h⟩ walk⟩
    · simp only [step,dite_eq_right live] at hit
      obtain ⟨n,le,walk⟩:=ih hit
      exact ⟨n,le.trans (Nat.le_succ _),walk⟩

theorem walk_digits {n : ℕ} {v z : Fin H} (walk : Walk peer n v z) :
    ∃xs : List (Fin (D+1)),xs.length=n ∧ follow peer xs (some v)=some z := by
  induction walk with
  | nil v=>exact ⟨[],rfl,rfl⟩
  | @cons n u v z edge rest ih=>
    obtain ⟨i,send⟩:=edge
    obtain ⟨xs,len,get⟩:=ih
    refine ⟨i.castSucc::xs,by simp [len],?_⟩
    change follow peer xs (step peer (some u) i.castSucc)=some z
    simpa only [step,Fin.val_castSucc,dite_eq_left i.isLt,Option.bind_some,send] using get

private theorem list_code (xs : List (Fin (D+1))) {n : ℕ} (len : xs.length=n) :
    ∃p : Fin ((D+1)^n),List.ofFn (finFunctionFinEquiv.symm p : Fin n→Fin (D+1))=xs := by
  subst n
  exact ⟨finFunctionFinEquiv xs.get,by simp⟩

theorem endpoint_iff (v z : Fin H) : (∃i,endpoints peer v i=some z) ↔ Reach peer v z := by
  constructor
  · rintro ⟨i,h⟩
    change follow peer (List.ofFn (finFunctionFinEquiv.symm i : Fin 10→Fin (D+1))) (some v)=some z at h
    simpa only [Reach,List.length_ofFn] using follow_walk peer _ h
  · rintro ⟨n,le,p⟩
    obtain ⟨xs,len,hit⟩:=walk_digits peer p
    let extra:=List.replicate (10-n) (Fin.last D)
    obtain ⟨i,hi⟩:=list_code (xs++extra) (n:=10) (by simp [extra,len];omega)
    refine ⟨i,?_⟩
    unfold endpoints
    rw [hi,follow_append,hit]
    exact follow_wait peer _ _

theorem present_iff (v z : Fin H) : z∈present (endpoints peer) v ↔ Reach peer v z := by
  simpa only [present,Finset.mem_filter,Finset.mem_univ,true_and] using endpoint_iff peer v z

theorem snoc {n : ℕ} {u v z : Fin H} (p : Walk peer n u v) (e : ∃i,peer v i=some z) :
    Walk peer (n+1) u z := by
  induction p with
  | nil _=>exact .cons e (.nil _)
  | cons edge _ ih=>exact .cons edge (ih e)

theorem reverse {n : ℕ} {u v : Fin H}
    (symm : ∀a b,(∃i,peer a i=some b)→∃i,peer b i=some a) (p : Walk peer n u v) :
    Walk peer n v u := by
  induction p with
  | nil _=>exact .nil _
  | cons edge _ ih=>exact snoc peer ih (symm _ _ edge)

theorem reciprocal (symm : ∀a b,(∃i,peer a i=some b)→∃i,peer b i=some a) (u v : Fin H) :
    Reach peer u v ↔ Reach peer v u := by
  constructor <;> rintro ⟨n,le,p⟩ <;> exact ⟨n,le,reverse peer symm p⟩

theorem card_bound (v : Fin H) : (present (endpoints peer) v).card≤(D+1)^10 := by
  classical
  let s:=present (endpoints peer) v
  have has (z : s) : ∃i,endpoints peer v i=some z.val := (Finset.mem_filter.mp z.property).2
  have unique : Function.Injective (fun z : s=>(has z).choose) := by
    intro a b h
    apply Subtype.ext
    exact Option.some.inj ((has a).choose_spec.symm.trans ((congrArg (endpoints peer v) h).trans (has b).choose_spec))
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective _ unique

theorem indexed_prefix (v : Fin H) (j : Fin ((D+1)^10)) (live : j.val<(present (endpoints peer) v).card) :
    oldWithin peer v j=some ((present (endpoints peer) v).orderEmbOfFin rfl ⟨j.val,live⟩) := by
  classical
  let s:=present (endpoints peer) v
  let e:=s.orderIsoOfFin rfl
  let i : Fin s.card:=⟨j.val,live⟩
  apply (indexed_iff _ _ _ _).mpr
  refine ⟨(e i).property,?_⟩
  change (s.filter (fun z=>z<(e i).val)).card=i.val
  rw [←Fin.card_Iio i]
  symm
  apply Finset.card_bij (fun j _=>(e j).val)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨(e j).property,e.strictMono (Finset.mem_Iio.mp hj)⟩
  · intro j _ k _ h;exact e.injective (Subtype.ext h)
  · intro z hz
    obtain ⟨mem,lt⟩:=Finset.mem_filter.mp hz
    let j:=e.symm ⟨z,mem⟩
    have eqn : e j=⟨z,mem⟩:=e.apply_symm_apply _
    have before : j < i:=e.lt_iff_lt.mp (show e j<e i by rw [eqn];exact lt)
    exact ⟨j,Finset.mem_Iio.mpr before,congrArg Subtype.val eqn⟩

private theorem before_lt_card {v z : Fin H} (mem : z∈present (endpoints peer) v) :
    before (endpoints peer) v z<(present (endpoints peer) v).card := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (Finset.filter_subset ..)).mpr
  exact ⟨z,mem,by simp⟩

theorem tail (v : Fin H) (i : Fin ((D+1)^10)) (hi : (present (endpoints peer) v).card ≤ i.val) :
    oldWithin peer v i=none := by
  cases out : oldWithin peer v i with
  | none=>rfl
  | some z=>
    obtain ⟨mem,eqn⟩:=(indexed_iff _ _ _ _).mp out
    have strict:=before_lt_card peer mem
    omega

/-- Exact length and order on each old host, before injecting the radix copy index. -/
def oldSet (v : Fin H) : Finset (Fin H) := present (endpoints peer) v

theorem oldWithin_eq_get (v : Fin H) (i : Fin ((D+1)^10)) :
    oldWithin peer v i=if live : i.val<(oldSet peer v).card then
      some ((oldSet peer v).orderEmbOfFin rfl ⟨i.val,live⟩) else none := by
  split
  next live=>exact indexed_prefix peer v i live
  next missing=>exact tail peer v i (Nat.le_of_not_gt missing)

theorem oldWithin_iff (v z : Fin H) : (∃i,oldWithin peer v i=some z) ↔ Reach peer v z := by
  classical
  constructor
  · rintro ⟨i,h⟩;exact (present_iff peer v z).mp ((indexed_iff _ _ _ _).mp h).1
  · intro accessible
    have mem:=(present_iff peer v z).mpr accessible
    have lt:=before_lt_card peer mem
    exact ⟨⟨_,lt.trans_le (card_bound peer v)⟩,(indexed_iff _ _ _ _).mpr ⟨mem,rfl⟩⟩

theorem ascending (v : Fin H) {i j : Fin ((D+1)^10)} {x y : Fin H}
    (left : oldWithin peer v i=some x) (right : oldWithin peer v j=some y) : x<y ↔ i<j := by
  obtain ⟨hx,rx⟩:=(indexed_iff _ _ _ _).mp left
  obtain ⟨hy,ry⟩:=(indexed_iff _ _ _ _).mp right
  constructor
  · intro lt
    change i.val<j.val
    simpa only [rx,ry] using before_strict _ hx lt
  · intro lt
    rcases lt_trichotomy x y with h|e|h
    · exact h
    · subst y;omega
    · have := before_strict _ hy h;omega

theorem «mutual» (symm : ∀a b,(∃i,peer a i=some b)→∃i,peer b i=some a) (v z : Fin H) :
    (∃i,oldWithin peer v i=some z) ↔ ∃i,oldWithin peer z i=some v := by
  exact (oldWithin_iff peer v z).trans ((reciprocal peer symm v z).trans (oldWithin_iff peer z v).symm)

theorem ghost (v : Fin H) (absent : ∀i,peer v i=none) (z : Fin H) :
    Reach peer v z ↔ z=v := by
  constructor
  · rintro ⟨n,_,p⟩
    cases p with
    | nil=>rfl
    | cons e _=>obtain ⟨i,h⟩:=e;rw [absent] at h;contradiction
  · rintro rfl;exact ⟨0,by decide,.nil _⟩

/-- Padding has one stay-only entry. The caller may suppress the whole receiver with its live bit. -/
theorem oldSet_ghost (v : Fin H) (absent : ∀i,peer v i=none) : oldSet peer v={v} := by
  ext z
  exact (present_iff peer v z).trans ((ghost peer v absent z).trans Finset.mem_singleton.symm)

theorem oldWithin_ghost (v : Fin H) (absent : ∀i,peer v i=none) (i : Fin ((D+1)^10)) :
    oldWithin peer v i=if i.val=0 then some v else none := by
  classical
  have set_eq : present (endpoints peer) v={v}:=oldSet_ghost peer v absent
  by_cases zero : i.val=0
  · rw [ite_eq_left zero]
    apply (indexed_iff _ _ _ _).mpr
    simp [set_eq, before,zero]
  · rw [ite_eq_right zero]
    apply tail peer
    rw [set_eq,Finset.card_singleton]
    omega

end
end Hierarchy.DescentTenHopRoster

end OAI
