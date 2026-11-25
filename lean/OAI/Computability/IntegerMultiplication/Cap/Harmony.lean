import OAI.Computability.IntegerMultiplication.Cap.Inverse

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Cap
open Finset Complex IntegerMultiplication.Fourier
variable {d:ℕ} (s:Bounds d) (q:Fin d→ℤ)
abbrev Along (s:Bounds d) := Vector_ s → ℂ

-- general reindexed tensor library
noncomputable def strand (k:(i:Fin d)→Spot (s i)→Spot (s i)→ℂ)
    (x:Along s) (v:Vector_ s) : ℂ :=
  ∑ y: Vector_ s,(∏ i,k i (v i) (y i))* x y

noncomputable def kernel {s:ℕ} (q:ℤ) (x y: Spot s) :ℂ :=
  phase s (-q*rep x*rep y)

noncomputable def sing (x:Along s) (t:Vector_ s) :=
  strand s (fun i=> kernel (q i)) x t

theorem strand_comp (k l:(i:Fin d)→ Spot (s i)→Spot (s i)→ℂ) (x:Along s) (v:Vector_ s):
    strand s k (strand s l x) v=
      strand s (fun i a b=>∑ u,k i a u * l i u b) x v := by
  classical
  unfold strand
  simp_rw [mul_sum,(show ∀ a b c:ℂ,a*(b*c)=(a*b)*c from fun a b c=> by ring)]
  rw [sum_comm]
  simp_rw [← prod_mul_distrib,Fintype.prod_sum,sum_mul]
-- orth sum one axis
theorem trio {s Q:ℕ} [NeZero s] (q : Nat.Coprime s Q)
    (x y z:Spot s) :
    ∑ t:Spot s,kernel (-(Q:ℤ)) z t*kernel (Q:ℕ) t x*kernel (Q:ℕ) t y=
      if x.val+y.val ≡ z.val [MOD s] then (s:ℂ) else 0 := by
  let K:ℤ:= Q*((z.val:ℕ)-(x.val+y.val:ℕ):ℤ)
  have h (t:Spot s) : kernel (-(Q:ℤ)) z t * kernel (Q:ℕ) t x*kernel (Q:ℕ) t y =
      phase s (K*(t.val:ℕ)) := by
    unfold kernel
    simp_rw [← phase_add]
    unfold K rep; congr 1; push_cast; ring
  simp_rw [h]
  rw [sum_phase]
  suffices H : (s:ℤ)∣ K ↔ x.val+y.val ≡ z.val [MOD s] by simp only [H]
  have e : (s:ℤ) ∣ K ↔ (Q*(x.val+y.val) ≡ Q*z.val [MOD s]) :=
    Iff.trans (by unfold K; rw [mul_sub]; push_cast; rfl)
      Nat.modEq_iff_dvd.symm -- metavars?
  rw [e]
  exact ⟨fun h=> Nat.ModEq.cancel_left_of_coprime q h, fun h=> h.mul_left _⟩
noncomputable def tonus (x y:Vector_ s) :=
  ∏ i,kernel (q i) (x i) (y i)
variable (Q:Fin d→ℕ) [∀ i,NeZero (s i)]
theorem mesh
    (p:∀ i,Nat.Coprime (s i) (Q i)) (x y z:Vector_ s):
    ∑ t:Vector_ s,
      tonus s (fun i=> -(Q i:ℤ)) z t*
        tonus s (fun i=>(Q i:ℤ)) t x * tonus s (fun i=>(Q i:ℤ)) t y=
      if (∀ i,(x i).val+(y i).val≡(z i).val [MOD s i])
      then ((space s:ℕ):ℂ) else 0 := by
  classical
  let H i (t:Spot (s i)): ℂ:=
    kernel (-(Q i:ℤ)) (z i) t*kernel (Q i:ℕ) t (x i)*kernel (Q i:ℕ) t (y i)
  have eq t: tonus s (fun i=> -(Q i:ℤ)) z t*tonus s (fun i=>(Q i:ℤ)) t x *
    tonus s (fun i=>(Q i:ℤ)) t y=∏ i,H i (t i) := by
    unfold tonus H; rw [← prod_mul_distrib, ← prod_mul_distrib]
  simp_rw [eq]
  have K:(∑ t:Vector_ s,∏ i,H i (t i))=∏ i,∑ t:Spot (s i), H i t:= (Fintype.prod_sum (κ:=fun i=>Spot (s i)) H).symm
  rw [K]
  simp_rw [show ∀ i,∑ t:Spot (s i), H i t=if (x i).val+(y i).val≡(z i).val [MOD s i] then (s i:ℂ) else 0 from fun i=> trio (p i) ..]
  split
  next h =>
    simp only [h, ↓reduceIte,space,Nat.cast_prod]
  next h=>
    obtain ⟨i,h⟩:=not_forall.mp h
    apply prod_eq_zero (mem_univ i) (ite_eq_right h)

/-- exact dft passes incl post normalization over vector.
Can use iterated strand one axis composition. -/
theorem renders (p:∀ i,Nat.Coprime (s i) (Q i)) (x y:Along s) (v:Vector_ s) :
    let f:=sing s (fun i=>(Q i:ℤ))
    let g:=sing s (fun i=> -(Q i:ℤ))
    g (fun z=> f x z*f y z) v / (space s:ℂ)=
    ∑ a:Vector_ s,∑ b:Vector_ s,
      if ∀ i,(a i).val+(b i).val≡(v i).val [MOD s i] then x a*y b else 0 := by
  classical
  let F:=tonus s (fun i=>(Q i:ℤ))
  let G:=tonus s (fun i=> -(Q i:ℤ))
  let M:ℂ:= space s
  have P : M ≠0 := by
    unfold M space
    exact_mod_cast ne_of_gt (Finset.prod_pos (fun i _=> Nat.pos_of_ne_zero (NeZero.ne _)))
  rw [div_eq_iff P]
  dsimp only [sing,strand]
  change ∑ w,G v w*((∑ a,F w a*x a)*(∑ b,F w b*y b)) = _*M
  have L : ∀ a b c d e:ℂ,a*(b*c*(d*e))=a*b*d*(c*e):=by intros; ring
  conv_lhs=>
    arg 2; ext w
    rw [sum_mul,mul_sum]
    simp only [mul_sum,L]
  rw [sum_comm]
  rw [sum_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm,sum_mul]
  refine sum_congr rfl fun b _=> ?_
  rw [← sum_mul, mesh s Q p]
  split <;> ring

end Cap

end IntegerMultiplication
end Computability
end OAI
