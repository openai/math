import OAI.Computability.IntegerMultiplication.Lea.Assembly

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- # Existence of a finite-alphabet multiplication TM with power saving. -/
open Param Scale Code Strip Bureau Cap Echo Dusk Cone Brief Dune Staff Carry Bits Lea Interface
variable (k n:ℕ)
theorem rewardP : 1≤ Param.reward n:=
  Real.one_le_rpow (by exact_mod_cast (show 1≤Param.beta _ from Nat.le_max_left 1 (Nat.clog 2 n))) (by norm_num)
theorem headP (h:1≤n):(n:ℝ)≤goalB n:=
  le_mul_of_one_le_right (by positivity) (rewardP n)
theorem headK (h:1≤n):1≤goalB n:=(show (1:ℝ)≤n by exact_mod_cast h).trans (headP n h)
-- restrict positive
abbrev Domain := {x:Inputs // 1≤ x.val.1.length}
abbrev v : Domain → Interface.Pair := fun x=> x.val.val
abbrev n0 (x:Domain):= (v x).1.length
theorem l1 (x:Domain) : (v x).2.length=n0 x:=x.val.2.symm
abbrev tags (x:Domain):Bool:=decide (n0 x < k)
noncomputable abbrev budgetB (x:Domain):ℝ:=goalB (n0 x)
theorem pos0(x:Domain):1≤budgetB x:=headK _ x.property
abbrev inpSt := send ∘ v
abbrev outSt := send ∘ Lea.answer ∘ v
theorem roomW (x:Domain) :
    ((inpSt x).count:ℝ)≤ 8*budgetB x:=by
  change (Code.size (v x):ℝ)≤_
  simp [size_word]
  rw [l1]
  change 2*(n0 x:ℝ)+1+(2*(n0 x:ℝ)+1)+1≤8*goalB (n0 x)
  have q: (1:ℝ)≤ goalB (n0 x):=pos0 x
  linarith [headP (n0 x) x.2,pos0 x]
-- tag true short program poly generic
private theorem fastHome : Poly answer := by
  have z:Poly Bits.product:=Bits.Poly.product_base
  unfold answer Bits.sized
  let f(y:Interface.Pair):= Code.ruler y.1 ++ Code.ruler y.1
  suffices e: Poly (fun y:Interface.Pair=> (Bits.resize (f y, Bits.product (y.1.reverse,y.2.reverse))).reverse) by
    have q(x:Interface.Pair): f x=Code.tally (2*x.1.length):=by unfold f;rw [← Code.recover_tally (Code.ruler x.1++Code.ruler x.1)]; simp [two_mul]
    simp_rw [q] at e; exact e
  have p : Poly (fun i: Code.Tally × Bits.Word => resize i):= (Bits.easy_resize Easy.identity).poly
  apply Poly.compose _ Easy.reverse.poly
  apply Poly.compose _ p
  have t : Poly f:=(show Easy f from by unfold f; fun_prop).poly
  apply t.pair
  exact (show Poly (fun y:Interface.Pair=> (y.1.reverse,y.2.reverse)) from (show Easy _ from by fun_prop).poly).compose z
abbrev shortS := {x: Domain // tags k x=true}
private theorem capS (x:shortS k):
    Code.size (v x.val) ≤ 8*(k+1) := by
  simp only [size_prod,size_word];rw [l1]
  change 2*n0 x.val+_+(_+_)+_≤_
  have q:n0 x.val<k:=of_decide_eq_true x.property
  omega
theorem winter :
    Sized (fun i:shortS k=>budgetB i.val) (fun i=> inpSt i.val) (fun i=>outSt i.val):= by
  obtain ⟨t,Y,h⟩:=fastHome
  obtain ⟨j,c,L⟩:=Y
  refine ⟨fun i=>pos0 _,_,(Task.on h (fun i: shortS k=> v i)), c*(8*(k+1)+1)^j+1,fun x=>?_⟩
  have p: t (v x.val)≤c*(8*(k+1)+1)^j := (L _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (capS k x) 1) _))
  exact (by exact_mod_cast (Nat.add_le_add_right p 1) :
    (t (v x.val):ℝ)+1 ≤ ↑(c*(8*(k+1)+1)^j+1)).trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (pos0 _))
abbrev longS := {x : Domain // tags k x=false}
-- union
theorem runs_ :
    Sized budgetB inpSt outSt := by
  obtain ⟨k,G⟩:= Filter.eventually_atTop.mp Scale.season
  have Y : Task (fun i=>⌈budgetB i⌉₊)
      (fun i : Domain=>send (tags k i,v i)) outSt := by
    apply Task.control (f:=inpSt) (tags k)
    · let A:= longS k
      let w(i:A):=n0 i.val
      have q(x:A):Season (w x):=G _ (Nat.le_of_not_gt (of_decide_eq_false x.property))
      have E:= large_ w q (fun i=> (v i.val).1) (fun i=> (v i.val).2) (fun _=>rfl) (fun i=>l1 _)
      exact E.runs.release
    exact (winter k).release
  have U : Sized budgetB (fun i : Domain=>send (tags k i,v i)) outSt :=
    ⟨pos0,_,Y,3,fun i=>by
      have p:=pos0 i
      have s:=Nat.ceil_lt_add_one (by linarith :0≤budgetB i)
      push_cast; linarith⟩
  let f : Interface.Pair→Bool:=fun x=> Iter.small (x.1,Code.tally k)
  have f0:Easy f:= (Easy.fst.pair (Easy.const _)).compose Iter.small_easy
  have E:= f0.pair (Easy.identity (X:=Interface.Pair))
  have H:= (Carries.func (y:=v) pos0 ⟨8,roomW⟩ _ E).runs
  have s (i:Domain): f (v i)=tags k i:= by unfold f Iter.small; simp
  simp_rw [s] at H; exact H.chain U

-- Compile!
theorem multiplication : Goal := by
  obtain ⟨p,b,h,j,u⟩:=runs_
  obtain ⟨A,Q,I,iS,qS,aS,s,S,B,i,o,a,g,K,D,F,f,G⟩:= Promise.stack (Y:=Domain) (q:=v) (w:=answer ∘ v) h
  refine ⟨A,Q,I,iS,qS,aS,s,S,B,i,o,a,g,K*(j+4),D,F,f,fun n H x y X Y=>?_⟩
  let d:Domain:=⟨⟨(x,y),X.trans Y.symm⟩,X ▸ H⟩
  obtain ⟨z,t,T,Z,U,N⟩:=G d
  have J:= date_length (v d)
  change (answer (v d)).length=2*x.length at J
  rw [X] at J
  refine ⟨z,t,answer (v d),T,Z,U,J,value_answer d.val.property,?_⟩
  change t≤K*(b d+x.length+y.length+ (answer (v d)).length+1) at N
  rw [J,X,Y] at N
  change (t:ℝ) ≤ ((K*(j+4):ℕ):ℝ)*(n:ℝ)* reward n
  have w : (b d:ℝ)+1 ≤ (j:ℝ)*((n:ℝ)*reward n):= by
    have w:=u d; rw [budgetB,n0] at w
    change _≤_*goalB x.length at w
    rwa [X] at w
  have W: (t:ℝ)≤ (K:ℝ)*(((b d:ℝ)+n+n+2*(n:ℝ)+1)):=by exact_mod_cast N
  push_cast
  have L : (n:ℝ) ≤ (n:ℝ)*reward n:=headP n H
  nlinarith [mul_le_mul_of_nonneg_left w (by positivity : 0≤(K:ℝ)),mul_le_mul_of_nonneg_left L (by positivity:0≤(K:ℝ))]

end IntegerMultiplication
end Computability
end OAI
