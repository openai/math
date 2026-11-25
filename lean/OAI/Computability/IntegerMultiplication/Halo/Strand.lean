import OAI.Computability.IntegerMultiplication.Halo.Group

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Halo
open Param Scale Echo Cap IntegerMultiplication.Fourier Finset Cone Grid Axon
noncomputable section
variable {n:ℕ} (h:Season n)
variable (x:primeV n) (y:sucV n) (z:dayV n) (a:Land n)
abbrev uX x y z:=gluer h (x,y,z)
abbrev Kx (v u:primeV n):ℂ:=∏ i:Scouts n,kernel (-(modulus n (rook i):ℤ)) (v i) (u i)
abbrev Ky (v u:sucV n):ℂ:=kernel (-(modulus n (near h):ℤ)) v u
abbrev Kz (v u:dayV n):ℂ:=kernel (-(modulus n (rear h):ℤ)) v u

theorem scanA : Fo h a (uX h x y z)=∑ v,Kx x v * a (uX h v y z) := by
  change xy (ell n) (Focn n) at x
  change orbit (sightA h) (trueC _) a ((sightA h).symm (x,y,z))=_
  rw [cup,trueExpansion]; unfold Kx
  simp_rw [Qu,pricedA h]
  rfl

private theorem solo {k:ℕ} (q:Fin 1→Bits.Word) (f:xy k 1→ℂ)(v:Spot (2^k)):
    trueC q f (lonely v)=
      ∑ u:Spot (2^k),kernel (-(Qu q 0)) v u * f (unscrew u) := by
  rw [trueExpansion,← (lonely (k:=k)).sum_comp (fun y=> (∏ i,kernel _ ((lonely v) i) (y i)) * f y)]
  apply sum_congr rfl; intro t _
  rw [Fin.prod_univ_succ]
  simp [lonely,unscrew]
-- each formula
theorem scanB : Fs h a (uX h x y z)=∑ v,Ky h y v * a (uX h x v z) := by
  change Spot (2^reach n) at y
  change orbit (sightB h) (trueC _) a ((sightB h).symm (lonely y,x,z))=_
  rw [cup,solo]; unfold Ky
  rw [show Qu (wordB h) 0=modulus n (near h) from congrArg Nat.cast (pricedN h _ (near_s h))]
  rfl

theorem scanC : Fl h a (uX h x y z)=∑ v,Kz h z v * a (uX h x y v) := by
  change Spot (2^ell n) at z
  change orbit (sightC h) (trueC _) a ((sightC h).symm (lonely z,x,y))=_
  rw [cup,solo]; unfold Kz
  rw [show Qu (wordC h) 0=modulus n (rear h) from congrArg Nat.cast (pricedN h _ (rear_f h))]
  rfl

theorem mounted (b c:Jade n) :
    ∏ i,Mounting n false i (gluer h b i) (gluer h c i)=
      Kx b.1 c.1*Ky h b.2.1 c.2.1 * Kz h b.2.2 c.2.2 := by
  unfold Kx Ky Kz Mounting mounting kernel rep
  rw [productF h]; simp [numeralP]
  simp_rw [rook_f,near_s h,rear_f h]

theorem glen_s : glen h = strand (criterion n) (Mounting n false) := by
  classical
  funext a b
  obtain ⟨⟨x,y,z⟩,rfl⟩ := (prism h).symm.surjective b
  change Fl h (Fs h (Fo h a)) (uX h x y z)=_
  rw [scanC]
  simp_rw [scanB,scanA,mul_sum]
  rw [sum_comm] -- y outside z x
  conv_lhs=> arg 2; ext u; rw [sum_comm] -- y x z
  rw [sum_comm] -- x y z
  unfold strand; rw [sums_ h]
  apply sum_congr rfl; intro v _
  apply sum_congr rfl; intro w _
  apply sum_congr rfl; intro t _
  change Kz h _ _ * (Ky h _ _ * (Kx _ _ * _)) = ((∏ i,Mounting n false i (gluer h (x,y,z) i) (gluer h (v,w,t) i))*a (uX h v w t))
  rw [mounted]
  ring

end
end Halo

end IntegerMultiplication
end Computability
end OAI
