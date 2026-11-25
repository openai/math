import OAI.Computability.IntegerMultiplication.Wave.Terminal
import OAI.Computability.IntegerMultiplication.Well.Stretch
import OAI.Computability.IntegerMultiplication.Cap.Straw

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Wave
open Param Scale Halo Strip Code Dims Cap Echo Well Bureau Carry Moira Staff Brief
variable {I:Type}(n:I→ℕ)(h:∀i,Season (n i))(a:(i:I)→Direction (n i))(u:Bool)
abbrev T0(i:I):Series (Tri (n i)):= road (criterion (n i)) u
abbrev X0(i:I):=prefixS (criterion (n i)) u (a i)
abbrev Y0(i:I):= suffixS (criterion (n i)) u (a i)
abbrev L0 i:=Well.axio n a i
abbrev A0(i:I):= Series.natural (L0 n a i)
theorem bill0(i:I):
    ct (X0 n a u) i*ct (A0 n a) i*ct (Y0 n a u) i=Cap.space (criterion (n i)):= by
  rw [Wave.space_sum _ u (a i)]
  change _*(Series.natural _).count*_ = _
  rw [Series.count_natural,mul_assoc]
include h
theorem atlas : Moira.Atlas n (X0 n a u) (A0 n a) (Y0 n a u) where
  l i:=posB ..
  m i:=by change _ ≤(Series.natural _).count; rw [Series.count_natural]; exact Nat.pos_of_neZero (L0 n a i)
  p i:=posA ..
  total i:=by rw [bill0]; change landscape _ ≤ _; rw [(h _).volume]; exact Nat.le_mul_of_pos_right _ (budget_p _)
omit h
variable {r:Regime I}(g:Guide r n)(e:Realizes r (fun i=> (a i).val))
include g e
theorem side_ :
    Figure r (L0 n a):=
  g.length_ n e
theorem name0 : Figure r (ct (A0 n a)):=by
  have F:ct (A0 n a)=L0 n a:=funext fun i=>Series.count_natural _
  rw [F];exact side_ n a g e

-- base or actual controls from header. lift Realizes a into varying u.
section
variable {R:I→ℕ} -- none
open Finset
theorem base_ (v:Bool):
    let s: (i:I)→Cap.Bounds (lanes (n i)) := fun i=> if v then criterion (n i) else modulus (n i)
    Figure r (fun i=> Cap.base (s i) (a i)):= by
  unfold Cap.base
  let d:= lanes ∘ n
  let w:=g.spread n
  apply (Cap.lists d w _ _).1
  let k : Across d→I:=Sigma.fst
  have G:=g.abroad n w
  have x:=floor_ d w
  have y:= landing d w _ e
  let t : Across d→ℕ:= fun i=>i.2.val
  cases v
  · exact (G.size_ (n ∘ k) x).variant (.natural 1) (Realizes.below x y)
  exact (G.length_ (n ∘ k) x).variant (.natural 1) (Realizes.below x y)
end
include h
omit e in
private theorem boon : Figure r (fun i=>Cap.space (criterion (n i))):= by
  change Figure _ (fun i=> landscape (n i))
  simp_rw [show ∀ i:I,landscape _=load (n i) from fun i=>(h i).volume]
  exact (Figure.natural 2).repeated (g.exSize n)
theorem chart : Figure r (ct (X0 n a u)) ∧ Figure r (ct (Y0 n a u)):= by
  have G: Figure r (fun i=>Cap.base (criterion (n i)) (a i)):=base_ n a g e true
  let a₀(i:I):=Cap.base (criterion (n i)) (a i)
  let q (i:I):=Cap.space (criterion (n i))/(a₀ i * L0 n a i)
  have Q : Figure r q := (boon n h g).quotients (G.multiplied (side_ n a g e))
  unfold ct
  cases u
  · change Figure r (fun i=>beforeS _ false (a i))∧Figure r (fun i=>afterS _ false (a i))
    simp_rw [baseA,show ∀ i:I,beforeS (criterion (n i)) false _=q i from fun i=>(complement _ (a i)).2]
    exact ⟨Q,G⟩
  · change Figure r (fun i=>beforeS _ true (a i))∧Figure r (fun i=>afterS _ true (a i))
    simp_rw [baseB,show ∀ i:I,afterS (criterion (n i)) true _=q i from fun i=>(complement _ (a i)).1]
    exact ⟨G,Q⟩
omit g e h
private theorem binary_ (i:I):
    ∃ k:ℕ, beforeS (criterion (n i)) true (a i)=2^k:= by
  rw [baseB]
  unfold Cap.base
  let t:=(n i)
  let s:= a i
  change ∃ k,(∏ j:Direction t,if j < s then 2^axle t j else 1)=2^k
  refine ⟨∑ j:Direction t,if j<s then axle t j else 0,?_⟩
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl; intro j _; split <;> rfl
abbrev countK(i:I):= Nat.clog 2 (ct (X0 n a true) i)
theorem shadow_ (i:I): (X0 n a true i).count=2^countK n a i := by
  obtain ⟨k,e⟩:=binary_ n a i
  change beforeS (criterion (n i)) true (a i) = 2^Nat.clog 2 (beforeS (criterion (n i)) true (a i))
  rw [e,Nat.clog_pow _ _ (by decide)] -- args
include g e h
theorem status_ : Realizes r (countK n a):= (chart n h a true g e).1.short_log

end Wave

end IntegerMultiplication
end Computability
end OAI
