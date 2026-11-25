import OAI.Computability.IntegerMultiplication.Code.Iter
import OAI.Computability.IntegerMultiplication.Loom.Arrivals

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Staff
open Strip Code Loom Dims Iter
def cash := Code.Tally
-- cash functions (use Tally abbrev!)
abbrev Buck := Code.Tally
abbrev box (k : ℕ) := tally k
abbrev bag (s : Buck) := s.length

variable {I : Type} (r : Regime I)
def Realizes (a : I → ℕ) :=
  r.Has (box ∘ a)
def Classified (f : I→Prop) := ∃ s:I→ Bool, r.Has s ∧ ∀ i,f i ↔ s i=true
variable {r}
theorem Classified.learn (s : I → Bool) (h : r.Has s) :
    Classified r (fun i=> s i=true) :=
  ⟨s,h,fun _=> Iff.rfl⟩

namespace Realizes
variable {u v : I→ℕ} (x : Realizes r u) (y : Realizes r v)
include x y
theorem plus :
    Realizes r (fun i=>u i+v i) := by
  simpa only [Realizes,Function.comp_def,Dims.mergeTally,box] using
    (Strip.Regime.Has.pair x y).ez Easy.append
theorem times :
    Realizes r (fun i=> u i*v i) := by
  have z := ((Strip.Regime.Has.pair x y).thenDo (Packed.chamber (X:=Tally))).ez Easy.flatten
  simp only [Function.comp_def,Realizes,box,List.map_const',tally_length,Dims.tallies] at z ⊢ -- map tally
  exact z
theorem minused :
    Realizes r (fun i=> u i-v i) := by
  have z := (Regime.Has.pair y x).ez (easy_cut easy_id).sndCompose
  simpa only [Function.comp_def,Realizes,box,cutLists,tally_length,tally,List.drop_replicate,List.length_replicate] using z
theorem below :
    Classified r (fun i=> u i<v i) := by
  refine ⟨fun i=> decide (u i<v i),?_,fun i=>by simp⟩
  simpa only [Function.comp_def,Realizes,box,Iter.small,tally_length] using (Regime.Has.pair x y).ez (Iter.small_easy (X:=Unit) (Y:=Unit))
omit x y in
theorem fix (k:ℕ) :
    Realizes r (fun _=> k) := Regime.fixed _
theorem select {p : I→Prop} [DecidablePred p] (t:Classified r p) :
    Realizes r (fun i=> if p i then u i else v i) := by
  obtain ⟨s,h,e⟩ := t
  have z := (h.pair (Regime.Has.pair y x)).ez (Easy.ifst Easy.fst Easy.snd)
  unfold Realizes
  convert z using 1
  funext i
  cases u:s i <;> have r:=e i <;> simp [u ▸ r]
end Realizes
-- Unary division. algorithm for mod 0 choose dividend.
abbrev divData := Buck × Buck -- accum Q and rem, forward in count.
def inject (x : Buck × divData) : divData :=
  let next := ()::x.2.2
  bif decide (next.length=x.1.length) then (()::x.2.1,[]) else (x.2.1,next)
@[fun_prop] theorem stable : Poly inject := by
  have e : Poly (fun x:Buck× Buck=> decide (x.1.length=x.2.length)) := linked.poly
  have z : Poly (fun x:Buck× divData=> decide ((()::x.2.2).length=x.1.length)) :=
    (Poly.compose (show Poly (fun x:Buck× divData=> (()::x.2.2,x.1)) from by fun_prop) e)
  unfold inject; dsimp only
  fun_prop

def quot (x : Buck × Buck) :=
  ((fun p => inject (x.2,p))^[x.1.length]) ([],[])
@[fun_prop] theorem stable_q : Poly quot := by
  have e := Poly.bounder inject stable 4 (by
    intro x y
    rcases y with ⟨p,q⟩
    unfold inject
    dsimp only
    rw [size_prod,size_tally,size_tally,size_tally]
    cases v : decide (((()::q).length)=x.length) -- ?
    all_goals simp only [Bool.cond_false,Bool.cond_true,List.length_cons,List.length_nil,size_prod,size_tally]; omega)
  exact (show Poly (fun x:Buck × Buck=> (x.1,x.2,([]:Buck),([]:Buck))) from by fun_prop).compose e

private theorem money (h:ℕ) (q : Buck) :
    ((fun p:divData=> inject (q,p))^[h]) ([],[])=(box (h/q.length),box (h%q.length)) := by
  by_cases y : q.length=0
  · induction h with
    | zero => simp [box,tally]
    | succ h ih =>
      rw [Function.iterate_succ_apply',ih]; simp [inject,y,box]
  induction h with
  | zero=> simp [box,tally]
  | succ h ih =>
    rw [Function.iterate_succ_apply', ih]
    have q₁ := Nat.mod_lt h (Nat.pos_of_ne_zero y)
    have q₂ := (Nat.div_add_mod h q.length) -- uses divisor first?
    have u : h=q.length*(h/q.length)+h%q.length := by simpa using (Nat.div_add_mod h q.length).symm
    unfold inject
    simp only [List.length_cons,box,tally_length]
    by_cases e : h%q.length+1=q.length <;> simp only [e,decide_true,decide_false,Bool.cond_true,Bool.cond_false]
    · have eq : h%q.length+1=q.length := by simpa using e
      have eq' : h+1=q.length*(h/q.length+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
      conv_rhs => rw [eq']
      simp [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero y)]
      rfl
    · have eq : h%q.length+1<q.length := by omega
      have eq' : h+1=q.length*(h/q.length)+(h%q.length+1) := by omega
      conv_rhs => rw [eq',Nat.add_comm (q.length*_),Nat.add_mul_mod_self_left,Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero y),Nat.div_eq_of_lt eq, Nat.mod_eq_of_lt eq]
      simp

@[simp] theorem quot_r (n k : ℕ) : quot (box n,box k)=(box (n/k),box (n%k)) := by
  unfold quot; simp [money,box]

namespace Realizes
variable {r : Regime I} {x y : I→ℕ} (v : Realizes r x) (w : Realizes r y)
include v w
theorem dividing :
    Realizes r (fun i=> x i/y i) := by
  simpa only [Realizes,Function.comp_def,quot_r] using
    (Regime.Has.pair v w).thenDo stable_q.fstCompose
theorem rem :
    Realizes r (fun i=>x i%y i) := by
  simpa only [Realizes,Function.comp_def,quot_r] using
    (Regime.Has.pair v w).thenDo stable_q.sndCompose
end Realizes
-- transfer Realizes premise across any Has tally from back transport
end Staff

end IntegerMultiplication
end Computability
end OAI
