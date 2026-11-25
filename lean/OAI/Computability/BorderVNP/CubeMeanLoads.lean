import OAI.Computability.BorderVNP.CubeMeanChoice

/-! # Conditional mean loads, endpoint incidence, and conserved totals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.MeanChoice

open Balancing Finset
open scoped BigOperators

variable {C E A : Type*} [Fintype C] [DecidableEq C] [Fintype E] [Fintype A] {z : ℕ}

/-- Ordered cable bins and single-symbol data-delivery bins. -/
abbrev Bins (z : ℕ) := (Fin (z+1) × Fin (z+1)) ⊕ Fin (z+1)

/-- Load functions for the two kinds of bins, on individual cable bits and data bits. -/
def loads (src dst : E → C) (recv : A → C) : Bins z → (C → Fin (z+1)) → ℝ
  | .inl (u,v) => Balancing.load (cable src dst u v)
  | .inr u => Balancing.load (datum recv u)

/-- Uniform target in each bin, before the first cell is pinned. -/
noncomputable def target (E A : Type*) [Fintype E] [Fintype A] (z : ℕ) : Bins z → ℝ
  | .inl _ => Fintype.card E/(z+1 : ℝ)^2
  | .inr _ => Fintype.card A/(z+1 : ℝ)

/-- Width of the cables or deliveries incident to the current cell. -/
def limits (src dst : E → C) (recv : A → C) (c : C) : Bins z → ℝ
  | .inl _ => (univ.filter (fun e => c ∈ ({src e,dst e} : Finset C))).card
  | .inr _ => (univ.filter (fun a => c = recv a)).card

omit [Fintype E] in
/-- A cable between distinct cells contributes precisely to the bin of the ordered pair of
its endpoint labels, also when those labels coincide. -/
theorem cable_hit {L : Type*} [DecidableEq L] (src dst : E → C) (h : ∀ e, src e ≠ dst e)
    (x : C → L) (e : E) (u v : L) :
    hit (cable src dst u v e) x = if (x (src e),x (dst e)) = (u,v) then 1 else 0 := by
  simp [hit,cable,(h e).symm, Prod.ext_iff]

omit [Fintype A] in
/-- A delivery contributes once, in the bin of its receiving cell. -/
theorem datum_hit {L : Type*} [DecidableEq L] (recv : A → C) (x : C → L) (a : A) (u : L) :
    hit (datum recv u a) x = if x (recv a) = u then 1 else 0 := by simp [hit,datum]

private theorem totals (src dst : E → C) (recv : A → C) (h : ∀ e, src e ≠ dst e)
    (x : C → Fin (z+1)) :
    (∑ j : Fin (z+1) × Fin (z+1), loads src dst recv (.inl j) x) = Fintype.card E ∧
    (∑ j : Fin (z+1), loads src dst recv (.inr j) x) = Fintype.card A := by
  constructor
  · change (∑ j : Fin (z+1) × Fin (z+1), ∑ e, hit (cable src dst j.1 j.2 e) x) = _
    rw [sum_comm]
    simp [cable_hit src dst h]
  · change (∑ j : Fin (z+1), ∑ a, hit (datum recv j a) x) = _
    rw [sum_comm]
    simp [datum_hit]

private theorem constant_target (src dst : E → C) (recv : A → C) (h : ∀ e, src e ≠ dst e)
    (x : C → Fin (z+1)) : dot (target E A z) (fun j => loads src dst recv j x) =
      (Fintype.card E/(z+1 : ℝ)^2) * Fintype.card E + (Fintype.card A/(z+1 : ℝ))* Fintype.card A := by
  obtain ⟨he, ha⟩ := totals src dst recv h x
  rw [dot,Fintype.sum_sum_type]
  dsimp only [target]
  rw [← mul_sum, ← mul_sum, he, ha]

/-- The scalar product with the uniform target stays constant under every pinning,
because each cable still has one ordered label pair and each datum one receiving label. -/
theorem conserve (src dst : E → C) (recv : A → C) (h : ∀ e, src e ≠ dst e)
    (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1)) :
    dot (target E A z) (mean (loads src dst recv) (insert c s) (Function.update x c v)) =
      dot (target E A z) (mean (loads src dst recv) s x) := by
  have fixed (s : Finset C) (x : C → Fin (z+1)) : dot (target E A z) (mean (loads src dst recv) s x) =
      (Fintype.card E/(z+1 : ℝ)^2)*Fintype.card E+(Fintype.card A/(z+1 : ℝ))*Fintype.card A := by
    unfold dot mean conditioned
    simp_rw [Finset.mul_expect]
    rw [← Finset.expect_sum_comm]
    change (𝔼 y, dot (target E A z) (fun j => loads src dst recv j (fill s x y))) = _
    simp_rw [constant_target src dst recv h]
    exact Fintype.expect_const _
  rw [fixed, fixed]

private theorem prob_bound {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L] (p : Pattern C L) (s : Finset C)
    (x : C → L) : 0 ≤ pinnedChance p s x ∧ pinnedChance p s x ≤ 1 := by
  have hz : 1 ≤ (Fintype.card L : ℝ) := by exact_mod_cast (show 1 ≤ Fintype.card L from Fintype.card_pos)
  have hzinv : (Fintype.card L : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz
  unfold pinnedChance
  split
  · exact ⟨by positivity, pow_le_one₀ (by positivity) hzinv⟩
  · norm_num

private theorem mean_count {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L] {I : Type*} [Fintype I]
    (p : I → Pattern C L) (s : Finset C) (x : C → L) :
    conditioned (Balancing.load p) s x = ∑ i, pinnedChance (p i) s x := by
  unfold conditioned Balancing.load
  rw [Finset.expect_sum_comm]; simp_rw [expect_pinned_hit]

private theorem jump_count {I : Type*} [Fintype I] (p : I → Pattern C (Fin (z+1)))
    (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1)) :
    |conditioned (Balancing.load p) (insert c s) (Function.update x c v) -
      conditioned (Balancing.load p) s x| ≤ (univ.filter fun i => c ∈ (p i).sites).card := by
  classical
  rw [mean_count,mean_count,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  rw [card_filter, Nat.cast_sum]
  apply sum_le_sum
  intro i _
  by_cases hc : c ∈ (p i).sites
  · simp only [hc,ite_true,Nat.cast_one]
    have h₁ := prob_bound (p i) (insert c s) (Function.update x c v)
    have h₂ := prob_bound (p i) s x
    rw [abs_le]; constructor <;> linarith
  · simp [hc,pinnedChance_unchanged (p i) s x c hc v]

/-- Fixing one cell changes a bin by at most the total incident width. Other cells'
already pinned labels are arbitrary. -/
theorem mean_jump (src dst : E → C) (recv : A → C) (s : Finset C) (x : C → Fin (z+1))
    (c : C) (v : Fin (z+1)) (j : Bins z) :
    |mean (loads src dst recv) (insert c s) (Function.update x c v) j -
      mean (loads src dst recv) s x j| ≤ limits src dst recv c j := by
  cases j with
  | inl j => exact jump_count (cable src dst j.1 j.2) s x c v
  | inr j => simpa [mean, loads, limits, datum] using jump_count (datum recv j) s x c v

/-- With no pinned cells, the mean vector is the uniform target, also for equal-label bins. -/
theorem mean_empty (src dst : E → C) (recv : A → C) (h : ∀ e, src e ≠ dst e) (x : C → Fin (z+1)) :
    mean (loads src dst recv) ∅ x = target E A z := by
  funext j
  cases j with
  | inl p =>
    change conditioned (Balancing.load (cable src dst p.1 p.2)) ∅ x = _
    rw [mean_count]
    simp [pinnedChance,cable,target,Finset.card_pair (h _),div_eq_mul_inv,inv_pow]
  | inr u =>
    change conditioned (Balancing.load (datum recv u)) ∅ x = _
    rw [mean_count]
    simp [pinnedChance,datum,target,div_eq_mul_inv]

/-- With every cell pinned the cached mean is exactly the actual bit load. -/
theorem mean_univ (src dst : E → C) (recv : A → C) (x : C → Fin (z+1)) :
    mean (loads src dst recv) univ x = fun j => loads src dst recv j x := by
  funext j
  have hf (y : C → Fin (z+1)) : fill univ x y = x := by funext c; simp [fill]
  simp [mean,conditioned,hf]

end Cube.MeanChoice

end BorderVNP
end Computability
end OAI
