import OAI.Computability.IntegerMultiplication.Atoll.Squall

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Param Scale Strip Code Dims Cap Halo Thin Loom Phase Earth Adic Packed Bureau Staff Brief Moira
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] (d:Guild J W L Net.Motif.sigma)(R:Series W)
variable (n:I→ℕ)(h:∀i,Season (n i))
variable (s:(i:I)→Series (ShadeV n i))(t:(i:I)→Series (Look n i))
variable (c:(i:I)→Adopt ((s i).cart (sk n i)) (t i))
variable (v:∀ i x,(c i).cast x=(x.1.1,x.1.2,x.2))
variable (u:∀ i,(s i).count=Bureau.dim n i)
variable (x:(i:I)→Look n i→ Cone.G (n i))
noncomputable section
abbrev flange :=
  stackRun (Moira.land s (sk n)) (fun i v=> wordV n x i v.1 v.2)
abbrev hull:= stackRun t (board n x)
include c v
theorem raw_r : hull n t x= flange n s x := by
  funext i
  rw [hull, stackRun,(c i).packet]
  change stripe _ _=stripe ((s i).cart (sk n i)) _
  apply congrArg (stripe _); funext a
  exact congrArg (board n x i) (v i a)
omit c v
include h u
private theorem cS i:ct s i=(Floorplan (n i)).count:=(u i).trans (tallH (h i))
omit h u in
private theorem cT i:ct (sk n) i=wall (n i):=tallZ _
private theorem amen_ :
    amen n s:= by
  let g:=guide_city n
  have W:= g.side_long n
  let a:= (Carry.Figure.natural 2).repeated (g.exSize n)
  have F:ct s=(fun i=>load (n i)/wall (n i)):= by
    funext i
    rw [cS n h s u i,← metric (h i)]
    exact (Nat.mul_div_cancel _ (Nat.pow_pos (by decide) : 0<wall (n i))).symm
  change Carry.Figure (city n) (ct s)
  rw [F]
  exact a.quotients W
omit h u in
private theorem amen_k :
    amen n (sk n) := by
  have F : ct (sk n) = wall ∘ n := funext (cT n)
  change Carry.Figure (city n) (ct (sk n))
  rw [F]
  exact (guide_city n).side_long n
omit h u in
private theorem size_s(i:I)(p:Look n i):
    (board n x i p).count ≤ 40000*P (n i):=by
  change size (Dusk.mark _)≤_
  rw [Dusk.volume]; have q:= near_ (n i); have j:0<P (n i):=budget_p _; omega
private theorem nail (i):
    ((s i).cart (sk n i)).count=load (n i):=
  (Series.count_cart ..).trans ((congrArg₂ Nat.mul (cS n h s u _) (cT n _)).trans (metric (h i)))
theorem fame : close n (flange n s x) := by
  refine ⟨41000,fun i=>?_⟩
  let k:=n i
  have e:=stripe_size ((s i).cart (sk n i))
    (fun p=> wordV n x i p.1 p.2) (40000*P k) (fun p=>size_s n x i (p.1.1,p.1.2,p.2))
  rw [nail n h s u] at e
  unfold token ton
  norm_cast
  have M: (load k)*(40000*P k+1)+1≤41000*(load k* P k):=by
    have q:1≤P k:=budget_p _
    have g:1≤load k:=Nat.pow_pos (by decide)
    nlinarith
  exact e.trans M

theorem broad : close n (horizonV n s x):=by
  refine ⟨43000,fun i=>?_⟩
  let k:=n i
  have g (a:ShadeV n i):
      (stripe (sk n i) (wordV n x i a)).count ≤ wall k*(40000*P k+1)+1:= by
    have q:= stripe_size (sk n i) (wordV n x i a) (40000*P k) (fun z=> size_s n x i (a.1,a.2,z))
    change _≤ct (sk n) i*(40000*P k+1)+1 at q; rwa [cT n] at q
  have e:=stripe_size (s i) _ _ g
  have M:= nail n h s u i
  rw [Series.count_cart] at M
  change _ * ct (sk n) _ = _ at M
  rw [cT n] at M
  unfold token ton
  norm_cast
  have W: (s i).count*(wall k*(40000*P k+1)+1+1)+1≤43000*(load k*P k):=by
    have q:1≤P k:=budget_p _
    have g:1≤ wall k:=Nat.pow_pos (by decide)
    have m: 1 ≤ load k:= Nat.pow_pos (by decide)
    change _*wall k=load k at M
    have V: 1 ≤ (s i).count * wall k := M ▸ m
    rw [← M] at *
    nlinarith [(show (s i).count ≤ (s i).count*wall k from Nat.le_mul_of_pos_right _ g),
      Nat.mul_le_mul_left (s i).count ((Nat.le_mul_of_pos_right _ q) : wall k ≤ wall k*P k)]
  exact e.trans W

include c v
theorem port0 : Wood n (hull n t x) (horizonV n s x):= by
  rw [raw_r n s t c v x]
  have B: Moira.bounded n s (sk n) := by
    refine ⟨fun i=> cS n h s u i ▸ place (h i),fun i=>cT n i ▸ (Nat.pow_pos (by decide) : 1≤wall (n i)),fun i=>?_⟩
    change _ ≤ load _* Scale.P _
    rw [cS n h s u i,cT n i,metric (h i)]
    exact Nat.le_mul_of_pos_right _ (budget_p _)
  exact Moira.paidG s (sk n) (fun i p=>wordV n x i p.1 p.2)
    (me (fame n h s u x)) B (amen_ n h s u) (amen_k n)
theorem port1 : Wood n (horizonV n s x) (hull n t x):= by
  rw [raw_r n s t c v x]
  exact Strip.flatten s (sk n) (fun i p=>wordV n x i p.1 p.2) (me (broad n h s u x))

end
end Atoll

end IntegerMultiplication
end Computability
end OAI
