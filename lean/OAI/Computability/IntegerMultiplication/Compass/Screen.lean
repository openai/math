import OAI.Computability.IntegerMultiplication.Olive.Axis
import OAI.Computability.IntegerMultiplication.Bureau.Tour
import OAI.Computability.IntegerMultiplication.Cone.Banner

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Compass
open Scale Param Strip Dims Code Halo Olive Echo Brief Bureau Grid Cone Phase Net Dusk
open Well
variable {I:Type}(n:I→ℕ)
variable (h:∀ i,Season (n i))(x y:(i:I)→Farm (n i))
abbrev V:=LandN n h
noncomputable section
abbrev tip (i:I):Farm (n i):= fun j=>punch (x i j) (y i j)
theorem point:
    Spun n (hue n) (together (V n h x) (V n h y)) (V n h (tip n x y)) := by
  let J(i:I):=Halo.walk (h i)
  let o(p:(i:I)→Farm (n i))(i:I)(a:Tri (n i)):=send (coda (n i) (p i) a)
  have e(p:(i:I)→Farm (n i)) :
      stackRun J (o p)=V n h p:=rfl
  let L:=together (V n h x) (V n h y)
  have g:= (sedan n h x).fork (sedan n h y) (chargep n)
  change close n L at g
  have Q:= me g
  let W := Scale.W ∘ n
  let F:= Scale.F ∘ n
  let v:= guide_city n
  let S:=Scale.birthday h
  let d:=Carry.Figure.repeated (Carry.Figure.natural (r:=city n) 2) ((guide_city n).exSize n)
  have ixx: Wood n L (fun i=>send (Code.tally (J i).count)) := by
    have Q:= (scoop g).chain (dispatchT (Param.load ∘ n) d (fun i=>Nat.le_mul_of_pos_right _ (budget_p _)))
    simpa only [J,census,Function.comp_def] using Q
  have f0:Wood n L (fun i=>send (Code.tally (F i))) := rescue g (S.fraction n)
  have B:= Strip.spread J (fun i=>send (Code.tally (F i))) (ixx.twice f0)
  have r : Wood n L (stackRun J fun i _=>send (Code.tally (F i))) := B (by
    refine ⟨20000,fun i=>?_⟩
    rw [census (h i)]
    change _*(size _:ℝ)≤_
    rw [size_tally,Code.tally_length]
    unfold token ton F Scale.F
    have p : 1≤(P (n i):ℝ):=by exact_mod_cast budget_p _
    have v : 1≤(load (n i):ℝ):=by exact_mod_cast (Nat.pow_pos (by decide):1≤load (n i))
    push_cast
    dsimp only [Function.comp_apply]
    push_cast
    nlinarith)
  have q(p:(i:I)→Farm (n i)): close n (V n h p):=sedan n h p
  have X:=Q.chain (Carries.dropRight Q.budget (q x) (q y))
  have Y:=Q.chain (Carries.dropLeft Q.budget (q x) (q y))
  rw [← e] at X Y -- might no occurrence L abbrev
  let A i (j:Tri (n i)): Tree:=send ((coda (n i) (x i) j),(Code.tally (F i),coda (n i) (y i) j))
  have U:Wood n L (stackRun J A):=
    Strip.coalesce J (o x) _ X (Strip.coalesce J _ _ r Y)
  let idx:=Σ i:I,Tri (n i)
  let root(v:idx):=v.1
  let f(v:idx): Grid.Orb:=(Code.tally (F v.1),coda _ (y v.1) v.2)
  have H:= Grid.ferry (W ∘ root) f (fun v:idx=> x v.1 v.2) 12 (by
    intro v
    unfold f; rw [size_prod]; dsimp only; rw [size_tally,Code.tally_length,coda,Function.comp_apply,Dusk.volume]
    have z: F v.1≤W v.1:=by unfold F W Scale.F Scale.W Function.comp; dsimp; omega
    change _≤12*(W v.1+1); change 2*F v.1+1+(4*(W v.1+1)+3)+1≤_; omega)
  have M:= liftoff J A (o (tip n x y)) (Grid.cost W) H
  rw [← e]
  have P0:= inherit U (color_p n)
  apply P0.chain
  obtain ⟨k,t⟩:= taxFund 8192
  apply M.times P0.budget (8193*k+1)
  intro i
  rw [show (J i).count=load (n i) from census (h i)]
  unfold Grid.cost grant token ton
  let m:=n i
  push_cast
  have p : (1:ℝ)≤Param.fund m:= Param.fund1 _
  have E:=mint_ n (color_p n) i
  have a : (W i:ℝ)+1 ≤ 8193*(P m):=by exact_mod_cast near_ m
  have b:(Grid.tax (W i):ℝ)≤ k*(Param.fund m):=
    calc
      _ ≤ Grid.tax (W i)*((span_ m:ℝ)+1):=le_mul_of_one_le_right (by positivity) (by simp)
      _ ≤ _ := t m _ (by unfold W Scale.W; change 8192*budget m≤_; omega)
  have L:= mul_le_mul a b (Nat.cast_nonneg _) (by have := budget_p m; positivity)
  have Z:= mul_le_mul_of_nonneg_left L (Nat.cast_nonneg (α:=ℝ) (load m))
  unfold grant token ton at E
  unfold m Bureau.hue at *
  push_cast at E
  nlinarith
end
end Compass

end IntegerMultiplication
end Computability
end OAI
