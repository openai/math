import OAI.Computability.IntegerMultiplication.Rivulet.Order
import OAI.Computability.IntegerMultiplication.Match
import OAI.Computability.IntegerMultiplication.Code.Iter

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Rivulet
open IntegerMultiplication.Fourier Strip Code
variable {s t:ℕ}[NeZero s][NeZero t] (h:s≤t)
variable {X:Type}[Codec X]
-- generic monotonic driver, consume blocks stutter <=2
abbrev uneven (s:Tally) (n:ℕ):Bool := Iter.small (s,tally n)
def render (x:X×Tally): List X:=
  bif uneven x.2 1 then [] else bif uneven x.2 2 then [x.1] else [x.1,x.1]
@[fun_prop] theorem render_E:Easy (render (X:=X)):= by
  have a(v):Easy (fun s:X×Tally=> uneven s.2 v):= by unfold uneven; exact (Easy.snd.pair (Easy.const _)).compose (Iter.small_easy (X:=Unit) (Y:=Unit))
  have m : Easy (fun v:X×Tally=> [v.1,v.1]) := by fun_prop
  have k : Easy (fun v:X×Tally=> [v.1]) := by fun_prop
  let sel (c:X×Tally→Bool) (f g:X×Tally→List X)(h:Easy c)(y:Easy f)(e:Easy g): Easy (fun i=>bif c i then f i else g i):=(h.pair Easy.identity).compose (Easy.ifst e y)
  exact sel _ _ _ (a _) (Easy.const _) (sel _ _ _ (a _) k m)
omit [Codec X] in
private theorem renders (x:X)(n:ℕ)(h:n≤2): render (x,tally n)=List.replicate n x:=by
  interval_cases n <;> rfl
variable (u:X)
def narrate (x:List X×List Tally):List X:=(lock render u [] x).flatten
@[fun_prop] theorem narrate_E:Easy (narrate u):=(easy_lock _ render_E u []).compose Easy.flatten
variable (g:Fin t→Fin s)
def plan :=List.ofFn (fun i=>tally (many g i))
-- full counts
omit [NeZero s] [NeZero t] [Codec X] in
theorem via (x: Fin s→X)(e:Monotone g)(w:∀i,many g i≤2):
    narrate u (List.ofFn x,plan g)=List.ofFn (x ∘ g) := by
  have q {X:Type}(f:Fin s→X): List.ofFn f=(Series.natural s).tab f := by
    change List.ofFn f=List.map f (List.finRange s)
    simp [List.finRange,Function.comp_def]
  rw [narrate,plan,q x,q (fun _=>_),paired,← List.map_ofFn]
  rw [← period _ e]
  simp_rw [renders _ _ (w _),Series.tab,flow]
  change (List.map _ (plate s)).flatten = List.map x (List.flatMap _ (plate s))
  simp only [List.flatMap]
  -- prove for any plate
  simp [Function.comp_def,List.map_replicate]

-- movement
variable (x:Fin t→X) (a:ℤ)
abbrev cropped := fun v:Fin s=>x ⟨v.val,v.isLt.trans_le h⟩
omit [NeZero s] [NeZero t] [Codec X] in
theorem excerpt :
    (List.ofFn x).take s=List.ofFn (cropped h x) := by
  refine List.ext_getElem ?_ (fun i t z=>?_); simp [h]
  simp [cropped]

abbrev aroundN (t:Tally)(x:List X) : List X :=
  let u:=cutLists (t,x)
  u.2++u.1
theorem aroundN_E : Easy (fun i:Tally×List X=>aroundN i.1 i.2):=
  let a:=easy_cut Easy.identity (X:=X)
  (a.compose Easy.exchange).compose Easy.append
abbrev cy (x:Fin s→X)(v:Fin s) := x (wrap s (rep v+a))
omit [Codec X] in
theorem circ (x:Fin s→X) :
    aroundN (tally (wrap s a).val) (List.ofFn x) = List.ofFn (cy a x) := by
  have p:= (wrap s a).isLt
  have P : (wrap s a).val < (List.ofFn x).length := by simp [p]
  suffices H : (List.ofFn x).rotate ((wrap s a).val)= List.ofFn (cy a x) by
    unfold aroundN cutLists; dsimp only; simpa only [tally_length, List.rotate_eq_drop_append_take_mod,Nat.mod_eq_of_lt P] using H
  apply List.ext_getElem (by simp)
  intro i v w
  have q:i<s:=by simpa using w
  let z:Fin s:=⟨i,q⟩
  rw [List.getElem_rotate,List.getElem_ofFn,List.getElem_ofFn]
  unfold cy
  congr 1
  apply Fin.ext
  have j (e): ((wrap s e).val:ℤ)=e%(s:ℤ):=rep_wrap _ _
  simp only [List.length_ofFn]
  change (i+(wrap s a).val)%s=(wrap s ((i:ℤ)+a)).val
  zify
  rw [j,j]; simp [Int.add_emod]
-- maps specs
abbrev p0 (v:Fin t): Fin t := ⟨(nextSample v a:Spot s).val,(nextSample v a:Spot s).isLt.trans_le h⟩
abbrev p1 (v:Fin t):Fin t :=
  if _e:v.val<s then pick s t h (wrap s ((v.val:ℤ)+a)) else v
-- Header per pass includes t', rep offset achieved raw.
abbrev Menu:= Tally × Tally × List Tally
abbrev menuA : Menu :=(tally s,tally (wrap s a).val,plan (river (s:=s) (t:=t)))
abbrev menuB : Menu :=(tally s,tally (wrap s a).val,plan (pick s t h))
variable {a h}
def ferryA (q:List X × Menu): List X :=
  let m:= cutLists (q.2.1,q.1)
  narrate u (aroundN q.2.2.1 m.1, q.2.2.2)
def ferryB (q:List X × Menu):List X :=
  let m:=cutLists (q.2.1,q.1)
  aroundN q.2.2.1 (narrate u (q.1,q.2.2.2))++m.2
@[fun_prop] theorem ferryA_E : Easy (ferryA u):=by
  have q : Easy (fun i:Tally×List X=>aroundN i.1 i.2) := aroundN_E
  unfold ferryA; dsimp only
  exact ((((Easy.snd.compose Easy.snd).fstCompose.pair (easy_cut ((Easy.snd.compose Easy.fst).pair Easy.fst)).fstCompose).compose q|>.pair ((Easy.snd.compose Easy.snd).compose Easy.snd)).compose (narrate_E u))
@[fun_prop] theorem ferryB_E : Easy (ferryB u):=by
  have q : Easy (fun i:Tally×List X=>aroundN i.1 i.2) := aroundN_E
  unfold ferryB
  exact ((Easy.snd.sndCompose.fstCompose.pair ((Easy.fst.pair Easy.snd.sndCompose.sndCompose).compose (narrate_E u))).compose q |>.pair (easy_cut (Easy.snd.fstCompose.pair Easy.fst)).sndCompose).compose Easy.append
-- crop append theorem
variable (a h)
include u
omit [Codec X] in
theorem trip0 (v:t≤2*s):
    ferryA u (List.ofFn x,menuA (s:=s) (t:=t) a)=List.ofFn (x ∘ p0 h a) := by
  unfold ferryA
  change narrate u (aroundN _ ((List.ofFn x).take _),_)=_
  rw [tally_length,excerpt h,circ,via u _ (cy a _) stead (m_f v)]
  rfl
include h
omit [NeZero s] [NeZero t] [Codec X] u in
private theorem append' (y:Fin s→X) (x:Fin t→X):
    List.ofFn y ++ (List.ofFn x).drop s= List.ofFn (fun v:Fin t=> if e:v.val<s then y ⟨v.val,e⟩ else x v) := by
  refine List.ext_getElem ?_ ?_
  · simp; omega
  intro i hi hj
  by_cases v:i<s
  · simp [List.getElem_append_left,v]
  have w : ¬i<(List.ofFn y).length := by simpa using v
  rw [List.getElem_append_right (Nat.le_of_not_lt w),List.getElem_drop,List.getElem_ofFn,List.getElem_ofFn]
  simp only [List.length_ofFn,dite_eq_right v]
  congr 2
  omega

omit [NeZero t] [Codec X] in
theorem trip1 :
    ferryB u (List.ofFn x,menuB h a)=List.ofFn (x ∘ p1 h a) := by
  unfold ferryB
  change aroundN _ (narrate u (List.ofFn x, _)) ++ (List.ofFn x).drop _=_
  rw [via u _ x (rise h).monotone (fun i=>(m_p h _).trans (by decide:1≤2)),tally_length,circ,append' h] -- args
  congr 1; funext v; unfold p1 Function.comp; split <;> simp_all [cy,rep]
  rw [ite_eq_right (by omega)]
end Rivulet

end IntegerMultiplication
end Computability
end OAI
