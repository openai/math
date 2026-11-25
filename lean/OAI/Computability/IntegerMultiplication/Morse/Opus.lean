import OAI.Computability.IntegerMultiplication.Morse.Buckle

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Morse
open Net Net.Walsh Strip Loom Adic Dusk Grid Axon Finset Code Bits
structure Lute where
  k:ℕ
  t:ℕ
  w:ℕ
  p:ℕ
  q:Bits.Word
  b:ℕ→Grain w
  x:Deck (k+1) t w
  ok:p≤w+1
noncomputable section
variable (i:Lute)
abbrev played : Order:= ⟨i.k+1,i.t,i.w,i.p,i.q,i.b,i.x,i.ok⟩
abbrev part (z:Face i.k):Panel:=⟨i.k,i.t,i.w,i.p,i.q,i.b,i.x,z,i.ok⟩
abbrev partialX (c:B) : Deck i.k i.t i.w:= fun v k=>ground (part i v) c k
abbrev notes := lease ∘ played
abbrev child (c:B) : Order:= ⟨i.k,i.t,i.w,i.p,i.q,doubleBank i.b,partialX i c,i.ok⟩
abbrev parts (i:Lute):= (PhaseL i.k).tab (fun v=>article (part i v))
abbrev brig := Scroll × Rows
def handle (x:brig) : List (Mat×card₀) :=
  let u:= x.1.headD []
  let h:=ruler u
  let a:= cutLists (h,x.2)
  let c:= lock id ([]:Seat) ([]:Seat) a
  let d:Dusk.Pair:=([],[])
  let e:Orb:=([],d)
  lock id (([]:Seat),([]:Seat)) (e,e) (c,u)
@[fun_prop] theorem handle_E : Easy handle := by
  unfold handle; dsimp only
  have y:= Iter.leader ([]:BlockT)
  have z:=easy_lock id Easy.identity ([]:Seat) ([]:Seat)
  have c:=easy_lock id Easy.identity (([]:Seat),([]:Seat)) ((([]:Tally),([]:Word),([]:Word)),([]:Tally),([]:Word),([]:Word))
  fun_prop
private theorem cutEq {X Y :Type} (c:List X)(l a:List Y)(h:l.length=c.length):
    cutLists (ruler c,l++a)=(l,a):= by simp [cutLists, ← h]
theorem handle_R :
    handle (prep (played i))=parts i := by
  unfold handle
  let t:=PhaseL i.k
  let u(c:B)(v:Face i.k):=slump (i.x (pre c v))
  let e:=shop i.p i.q i.b (k:=i.k)
  let d:Dusk.Pair:=([],[])
  let A:Orb:=([],d)
  have V:card i.x=t.tab (u 0)++t.tab (u 1):= follow_pre ..
  change lock id (([]:Seat),([]:Seat)) (A,A)
    (lock id ([]:Seat) ([]:Seat) (cutLists (ruler (t.tab e),card i.x)),t.tab e)=_
  rw [V,cutEq _ _ _ (by simp),paired,paired]; rfl

abbrev nr (x:Lute):ℝ:=lease (played x)
def follow {X} (l:List X):List X:=l.tail
@[fun_prop] theorem follow_E {X:Type}[Codec X]:Easy (follow (X:=X)) :=
  let e : follow = fun (l:List X)=> List.casesOn (motive:=fun _=>List X) l [] (fun _ t=> t) :=
    funext fun l=> by cases l <;> rfl
  e ▸ Easy.listCase [] Easy.snd

theorem funds (x:Lute):
    (size (prep (played x)):ℝ) ≤ 50*nr x := by
  have e:= board (played x); have t:= price1 (played x)
  change size (prep ..)≤_ at e
  exact_mod_cast (e.trans (Nat.mul_le_mul_left _ t))
theorem lpos(x:Lute):1≤nr x:=price3 _

def ship2 (x: List (Seat × Seat) × Scroll) : List brig×Rows:=
  ([(x.2,x.1.map Prod.fst), (x.2,x.1.map Prod.snd)],[])
@[fun_prop] theorem ship2_E:Easy ship2:=by unfold ship2; fun_prop
abbrev package (i:Lute):= ship2 ((PhaseL i.k).tab fun v=> duoR (part i v),scroll i.p i.q (doubleBank i.b) i.k)

set_option maxHeartbeats 1000000 in
theorem delivered : Carries nr (ready ∘ played) (fun i=>send (package i)) := by
  have m:=Carries.idles lpos (p:=fun x=>send (prep (played x))) (show Volume nr _ from
    ⟨50,fun i=>by rw [Nat.cast_ofNat]; exact funds _⟩)
  have k:=m.chain (Carries.func lpos m.out handle handle_E)
  have t:=m.chain (Carries.func lpos m.out (fun i:brig=>follow i.1) (by fun_prop))
  let P (i:Lute):= PhaseL i.k
  let X (i:Lute)(v:Face i.k):=send (duoR (part i v))
  have j : Carries nr (ready ∘ played) (stackRun P fun i v=>send (article (part i v))) := by
    unfold stackRun
    simp_rw [stripe_eq']
    simp_rw [handle_R] at k
    exact k
  let r (i:Lute):ℝ:=(i.t+1:ℝ)* Grid.cost (fun (i:Lute)=>i.w) i
  have R(i:Lute):1≤r i:=one_le_mul_of_one_le_of_one_le (by simp) (cost_pos ..)
  have M := liftoff P (fun i v=>send (article (part i v))) X r
    (cross.slide (fun s:Σ i:Lute,Face i.k=>part s.1 s.2))
  have v (i:Lute) : ((P i).count:ℝ)*r i+1 ≤nr i := by
    have A := R i
    change _ ≤ ((2^(i.k+1)*(i.t+1)*(i.w+1)*_ :ℕ):ℝ)
    push_cast
    rw [phase_size]
    push_cast
    have q : (1:ℝ)≤ (2:ℝ)^i.k:= one_le_pow₀ (by norm_num)
    rw [pow_succ]
    have j:= one_le_mul_of_one_le_of_one_le q A
    unfold r Grid.cost at *
    nlinarith -- lambda
  have u := j.chain (M.larger (d:=nr) v)
  let Y (i:Lute):= (P i).tab (fun v=>duoR (part i v))
  have U: Carries nr (ready ∘ played) (send ∘ Y):=by
    unfold stackRun at u
    change Carries _ _ (fun i=>stripe (P i) (fun v=>send (duoR (part i v)))) at u
    simp_rw [stripe_eq'] at u; exact u
  have H:= U.twice t
  exact H.chain (Carries.func (y:=fun i=> (Y i,follow (prep (played i)).1)) H.budget H.out ship2 ship2_E)

-- outputs equal to child preps
theorem bills :
    send (package i)=Tree.fork (Task.forest ready [child i 0,child i 1]) (send ([]:Rows)) := by
  let S:=PhaseL i.k
  unfold package ship2
  rw [send_prod]
  congr 1
  simp only [Series.map_tab]
  rfl

-- universal recovery
abbrev mail:= List Rows × Rows
def aliveR (l:List Rows):Bool:= Iter.small (([]:List Rows),l)
def post (x:mail):Rows:=
  bif aliveR x.1 then (lock duo ([]:Seat) ([]:Seat) (x.1.headD [],(follow x.1).headD [])).flatten else x.2
@[fun_prop] theorem post_E:Easy post := by
  have q : Easy (fun i:mail=>aliveR i.1):=by unfold aliveR; have y:=Iter.small_easy (X:=Rows) (Y:=Rows); fun_prop
  have c (l:Rows):Easy (fun i:List Rows=>i.headD l):=Iter.leader _
  have f:Easy (lock duo ([]:Seat) ([]:Seat)):= easy_lock duo (by unfold duo; fun_prop) ..
  apply easy_bool _ _ _ q _ Easy.snd
  fun_prop
set_option maxHeartbeats 850000 in
theorem post_L :
    post ([cure (child i 0),cure (child i 1)],[])= cure (played i) := by
  let F(v:Face (i.k+1)):=slump (fun z=> study (played i) (played i).x v z)
  have Q (b:B)(v:Face i.k):
      (slump (study (child i b) (partialX i b) v))=F (fan v b) := by
    unfold F; congr 1; funext z; exact (thermal i.p i.q i.b (fun v=>i.x v z) v b).symm
  unfold post; dsimp only
  rw [show aliveR ([cure (child i 0),cure (child i 1)])=true from rfl,Bool.cond_true]
  change (lock _ _ _ ((PhaseL i.k).tab _, (PhaseL i.k).tab _)).flatten=_
  refine Eq.trans ?_ (w_l (k:=i.k) F [])
  simp_rw [← Q]
end
end Morse

end IntegerMultiplication
end Computability
end OAI
