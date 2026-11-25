import OAI.Computability.BorderVNP.CubeMeanLoads

/-! # Uniform load bounds of the public mean-increment labeling -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.MeanChoice

open Finset Balancing
open scoped BigOperators

variable {C E A : Type*} [Fintype C] [DecidableEq C] [Fintype E] [Fintype A] {z : ℕ}

private def cableInc (src dst : E → C) (c : C) : ℕ := (univ.filter fun e => c ∈ ({src e,dst e} : Finset C)).card

private def dataInc (recv : A → C) (c : C) : ℕ := (univ.filter fun a => c = recv a).card

private theorem cable_total (src dst : E → C) (hne : ∀ e, src e ≠ dst e) :
    ∑ c, cableInc src dst c = 2*Fintype.card E := by
  simp only [cableInc,card_filter]
  rw [sum_comm]
  have each (e : E) : (∑ c : C, if c ∈ ({src e,dst e} : Finset C) then 1 else 0 : ℕ) = 2 := by
    rw [Fintype.sum_ite_mem, Finset.sum_const, Finset.card_pair (hne e)]
    rfl
  simp only [each, sum_const, card_univ, smul_eq_mul]; omega

private theorem data_total (recv : A → C) : ∑ c, dataInc recv c = Fintype.card A := by
  simp only [dataInc,card_filter]
  rw [sum_comm]; simp

omit [DecidableEq C] in
private theorem charge_le (inc : C → ℕ) (M : ℕ) (h : ∀ c, inc c ≤ M) :
    (∑ c, (inc c : ℝ)^2) ≤ (M : ℝ)*(∑ c, inc c : ℕ) := by
  rw [Nat.cast_sum,mul_sum]
  apply sum_le_sum; intro c _
  rw [sq]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast h c) (Nat.cast_nonneg _)

/-- The full squared-incidence charge uses each endpoint of each cable and exactly one
receiving cell for each delivered bit. -/
theorem incidence_budget (src dst : E → C) (recv : A → C) (W : ℝ) (M : ℕ)
    (hne : ∀ e, src e ≠ dst e) (he : (Fintype.card E : ℝ) ≤ 2*W) (ha : (Fintype.card A : ℝ) ≤ W)
    (hm : ∀ c, (univ.filter fun e => c ∈ ({src e,dst e} : Finset C)).card ≤ M)
    (hd : ∀ c, (univ.filter fun a => c = recv a).card ≤ M) :
    (∑ c, ∑ j : Bins z, (limits src dst recv c j)^2) ≤
      (z+1 : ℝ)^2*(4*W*M)+(z+1 : ℝ)*(W*M) := by
  have hE := charge_le (cableInc src dst) M hm
  have hA := charge_le (dataInc recv) M hd
  rw [cable_total src dst hne, Nat.cast_mul, Nat.cast_ofNat] at hE
  rw [data_total recv] at hA
  have ec : (∑ c, (cableInc src dst c : ℝ)^2) ≤ 4*W*M := calc
    _ ≤ (M:ℝ)*(2*Fintype.card E) := hE
    _ ≤ (M:ℝ)*(2*(2*W)) := by gcongr
    _ = _ := by ring
  have ac : (∑ c, (dataInc recv c : ℝ)^2) ≤ W*M := calc
    _ ≤ (M:ℝ)*Fintype.card A := hA
    _ ≤ (M:ℝ)*W := by gcongr
    _ = _ := mul_comm _ _
  have hrow (c : C) : (∑ j : Bins z, (limits src dst recv c j)^2) =
      (z+1 : ℝ)^2*(cableInc src dst c : ℝ)^2+(z+1 : ℝ)*(dataInc recv c : ℝ)^2 := by
    rw [Fintype.sum_sum_type]
    simp [limits, cableInc, dataInc, sq]
  simp_rw [hrow]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  exact add_le_add (mul_le_mul_of_nonneg_left ec (sq_nonneg _))
    (mul_le_mul_of_nonneg_left ac (by positivity))

/-- The mean-increment algorithm satisfies Lemma 8.2 on any duplicate-free visiting order
covering the cells, with precisely the manuscript's volume and variance slack. -/
theorem balanced (src dst : E → C) (recv : A → C) (cs : List C) (nodup : cs.Nodup)
    (cover : cs.toFinset = univ) (W : ℝ) (M : ℕ)
    (hne : ∀ e, src e ≠ dst e) (he : (Fintype.card E : ℝ) ≤ 2*W) (ha : (Fintype.card A : ℝ) ≤ W)
    (hm : ∀ c, (univ.filter fun e => c ∈ ({src e,dst e} : Finset C)).card ≤ M)
    (hd : ∀ c, (univ.filter fun a => c = recv a).card ≤ M)
    (slack : (z+1 : ℝ)^2*(4*W*M)+(z+1 : ℝ)*(W*M) ≤ (W/(z+1 : ℝ)^2)^2) :
    let label := follow (loads (z := z) src dst recv) cs ∅ (fun _ => 0)
    (∀ u v, Balancing.load (cable src dst u v) label ≤ 4*W/(z+1 : ℝ)^2) ∧
      ∀ u, Balancing.load (datum recv u) label ≤ 4*W/(z+1 : ℝ) := by
  intro label
  have hW : 0 ≤ W := (Nat.cast_nonneg _).trans ha
  have hr := follow_le (loads (z := z) src dst recv) cs ∅ (fun _ => 0) (target E A z)
    (limits src dst recv) (conserve src dst recv hne) (mean_jump src dst recv)
  rw [← List.sum_toFinset _ nodup,cover,union_empty,mean_univ,mean_empty src dst recv hne] at hr
  have budget := incidence_budget (z:=z) src dst recv W M hne he ha hm hd
  have herr : energy (fun j => loads src dst recv j label) (target E A z) ≤ (W/(z+1 : ℝ)^2)^2 := by
    have hz : energy (target E A z) (target E A z) = 0 := by simp [energy]
    rw [hz,zero_add] at hr
    exact hr.trans (budget.trans slack)
  have one (j : Bins z) : loads src dst recv j label ≤ target E A z j + W/(z+1 : ℝ)^2 := by
    have hs := Finset.single_le_sum (f := fun k => (loads src dst recv k label-target E A z k)^2)
      (fun k _ => sq_nonneg _) (mem_univ j)
    have hsq := hs.trans herr
    have habs : |loads src dst recv j label-target E A z j| ≤ W/(z+1 : ℝ)^2 :=
      (sq_le_sq₀ (abs_nonneg _) (div_nonneg hW (sq_nonneg _))).mp (by simpa using hsq)
    linarith only [le_abs_self (loads src dst recv j label-target E A z j), habs]
  constructor
  · intro u v
    have h := one (.inl (u,v))
    change Balancing.load (cable src dst u v) label ≤ Fintype.card E/(z+1 : ℝ)^2 + W/(z+1 : ℝ)^2 at h
    have hdiv := div_le_div_of_nonneg_right he (sq_nonneg (z+1:ℝ))
    rw [mul_div_assoc] at hdiv ⊢
    linarith only [h,hdiv,div_nonneg hW (sq_nonneg (z+1:ℝ))]
  · intro u
    have h := one (.inr u)
    change Balancing.load (datum recv u) label ≤ Fintype.card A/(z+1 : ℝ)+W/(z+1 : ℝ)^2 at h
    have hz : 1 ≤ (z+1:ℝ) := by linarith only [Nat.cast_nonneg (α:=ℝ) z]
    have hzpos : 0 < (z+1:ℝ) := by positivity
    have hdiv := div_le_div_of_nonneg_right ha hzpos.le
    have hw : W/(z+1 : ℝ)^2 ≤ W/(z+1:ℝ) := div_le_div_of_nonneg_left hW hzpos
      (by nlinarith only [hz,mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1) hz])
    rw [mul_div_assoc]
    linarith only [h,hdiv,hw,div_nonneg hW hzpos.le]

end Cube.MeanChoice

end BorderVNP
end Computability
end OAI
