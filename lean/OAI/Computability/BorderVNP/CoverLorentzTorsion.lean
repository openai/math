import OAI.Computability.BorderVNP.CoverLorentzIndex
import Mathlib.GroupTheory.OrderOfElement

/-!
# Separation and torsion in the congruence tower

The principal congruence kernels separate integral quaternion units. A nontrivial
unit at positive depth has infinitely many distinct seventh powers, because each
seventh power raises its exact depth by one. This proves the torsion assertion of §5.1.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

/-- Monotonicity of the principal norm-one subgroups in the level. -/
theorem gamma_antitone : Antitone gamma := by
  intro i j hij
  induction hij with
  | refl => exact le_rfl
  | step h ih => exact (gamma_next _).trans ih

private theorem zero_of_divisible_at_all_depths (a : ℤ)
    (h : ∀ d : ℕ, (7:ℤ)^(d+1) ∣ a) : a = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h a.natAbs)
  have hs := Nat.lt_pow_self (n := a.natAbs+1) (by decide : 1 < 7)
  simpa [Int.natAbs_pow] using (Nat.lt_succ_self a.natAbs).trans hs

/-- Only the identity belongs to every positive congruence level. -/
theorem eq_one_of_mem_all {u : Orderˣ} (h : ∀ d, u ∈ gamma (d+1)) : u = 1 := by
  have hdiv (π : Order →ₗ[ℤ] ℤ) (d : ℕ) : (7:ℤ)^(d+1) ∣ π ((u:Order)-1) := by
    obtain ⟨_,x,hx⟩ := h d
    exact ⟨π x,by rw [hx,atDepth,add_sub_cancel_left,map_smul]; rfl⟩
  have hzero : (u:Order) - 1 = 0 := by
    ext
    · exact zero_of_divisible_at_all_depths _ (hdiv (QuaternionAlgebra.reₗ 2 0 3))
    · exact zero_of_divisible_at_all_depths _ (hdiv (QuaternionAlgebra.imIₗ 2 0 3))
    · exact zero_of_divisible_at_all_depths _ (hdiv (QuaternionAlgebra.imJₗ 2 0 3))
    · exact zero_of_divisible_at_all_depths _ (hdiv (QuaternionAlgebra.imKₗ 2 0 3))
  exact Units.ext (sub_eq_zero.mp hzero)

/-- Membership in level `d+1` with nonzero coefficient in its quotient by level `d+2`. -/
def ExactDepth (d : ℕ) (u : Orderˣ) : Prop := u ∈ gamma (d+1) ∧ u ∉ gamma (d+2)

/-- Every nonidentity unit of the base group has a unique first nonzero coefficient. -/
theorem exists_exactDepth {u : Orderˣ} (hu : u ∈ gamma 1) (hne : u ≠ 1) :
    ∃ d, ExactDepth d u := by
  classical
  have some : ∃ k, u ∉ gamma (k+1) := by
    by_contra! h
    exact hne (eq_one_of_mem_all h)
  have hs := Nat.find_spec some
  have hpos : Nat.find some ≠ 0 := fun e => by rw [e] at hs; exact hs hu
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  refine ⟨d, ?_, by rwa [hd] at hs⟩
  by_contra h
  exact Nat.find_min some (by omega : d < Nat.find some) h

/-- Seventh powers raise the exact congruence depth by one. -/
theorem ExactDepth.seventh {u : Orderˣ} {d : ℕ} (h : ExactDepth d u) :
    ExactDepth (d+1) (u^7) := by
  let g : gamma (d+1) := ⟨u,h.1⟩
  let x := coefficient (d+1) g
  have hx : (u:Order) = atDepth (d+1) x := coefficient_spec _ g
  have hn : norm (u:Order) = 1 := g.2.1
  have hr : residues x ≠ 0 := by
    intro he
    have hm : g ∈ (leading d).ker := he
    rw [leading_kernel] at hm
    exact h.2 hm
  obtain ⟨y,hy,he⟩ := depth_seventh d x
  have hz : ((u^7 : Orderˣ) : Order) = atDepth (d+2) y := by
    rw [Units.val_pow_eq_pow_val,hx,hy]
  have hg : u^7 ∈ gamma (d+2) := ⟨by rw [Units.val_pow_eq_pow_val,norm_pow,hn,one_pow],y,hz⟩
  refine ⟨hg,?_⟩
  intro deeper
  let v : gamma (d+2) := ⟨u^7,hg⟩
  have hv : v ∈ (leading (d+1)).ker := (leading_kernel _).symm ▸ deeper
  change residues (coefficient (d+2) v) = 0 at hv
  have hcoeff : coefficient (d+2) v = y := atDepth_inj _ ((coefficient_spec _ v).symm.trans hz)
  rw [hcoeff,residues_congr he] at hv
  exact hr hv

private theorem exactDepth_unique {u : Orderˣ} {d e : ℕ}
    (hd : ExactDepth d u) (he : ExactDepth e u) : d = e := by
  rcases lt_trichotomy d e with h|h|h
  · exact (hd.2 (gamma_antitone (show d+2 ≤ e+1 by omega) he.1)).elim
  · exact h
  · exact (he.2 (gamma_antitone (show e+2 ≤ d+1 by omega) hd.1)).elim

/-- The base group of the cover is torsion-free. -/
theorem eq_one_of_finite_order {u : Orderˣ} (hu : u ∈ gamma 1) (h : IsOfFinOrder u) :
    u = 1 := by
  by_contra hne
  obtain ⟨d,hd⟩ := exists_exactDepth hu hne
  have hp (k : ℕ) : ExactDepth (d+k) (u^(7^k)) := by
    induction k with
    | zero => simpa only [pow_zero,pow_one,Nat.add_zero] using hd
    | succ k ih => simpa only [pow_succ (7 : ℕ), pow_mul, Nat.add_assoc] using ih.seventh
  let f (k : ℕ) : Subgroup.zpowers u := ⟨u^(7^k),Subgroup.npow_mem_zpowers _ _⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he : u^(7^i) = u^(7^j) := congrArg Subtype.val hij
    have hdep := exactDepth_unique ((he ▸ hp i) : ExactDepth (d+i) (u^(7^j))) (hp j)
    omega
  have := h.finite_zpowers
  exact not_injective_infinite_finite f hf

end Cover

end BorderVNP
end Computability
end OAI
