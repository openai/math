import OAI.ThreeFlat.ExpanderCloudStep

namespace OAI
/-! # Iterating cloud replacement at a uniform bound -/

namespace ThreeFlat.Expander

open Finset Computability.VPVNP.SpectralGeometry
open scoped BigOperators
universe u

variable {V W X : Type*} [Fintype V] [Fintype W] [PseudoMetricSpace X]

theorem variance_equiv (e : W ≃ V) (x : V → X) : variance (x ∘ e) = variance x := by
  calc
    _ = avg (fun i : W => avg (fun j : V => dist (x (e i)) (x j)^2)) :=
      avg_congr _ _ fun i => avg_equiv e (fun j => dist (x (e i)) (x j)^2)
    _ = _ := avg_equiv e (fun i => avg (fun j => dist (x i) (x j)^2))

theorem energy_transition_equiv (e : W ≃ V) (c : V → V → ℕ) (b : ℕ) (x : V → X) :
    energy (transition (fun i j => c (e i) (e j)) b) (x ∘ e) =
      energy (transition c b) x := by
  calc
    _ = avg (fun i : W => ∑ j : V, transition c b (e i) j * dist (x (e i)) (x j)^2) :=
      avg_congr _ _ fun i => e.sum_comp (fun j => transition c b (e i) j * dist (x (e i)) (x j)^2)
    _ = _ := avg_equiv e (fun i => ∑ j, transition c b i j * dist (x i) (x j)^2)

theorem Bound.transition_reindex (e : W ≃ V) (c : V → V → ℕ) {b : ℕ} {γ : ℝ}
    (bound : Bound (transition c b) X γ) :
    Bound (transition (fun i j => c (e i) (e j)) b) X γ := by
  intro x
  let y := x ∘ e.symm
  have h : x = y ∘ e := funext fun i => by simp [y]
  rw [h, variance_equiv, energy_transition_equiv]
  exact bound y

theorem energy_transition_nonneg (c : V → V → ℕ) (b : ℕ) (x : V → X) :
    0 ≤ energy (transition c b) x :=
  avg_nonneg fun _ => sum_nonneg fun _ _ =>
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)

/-- An inner graph whose Poincaré constant is small compared with the walk
length gives a family of uniformly bounded-degree graphs on the powers of
its order. Each member works simultaneously for every complete CAT(0)
target on which the inner graph satisfies the indicated bound. -/
theorem exists_cloud_expander_family {h k q : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hq : 0 < q) (hd : (2*k) * (4*h)^(2*k) ∣ q)
    (H : Fin q → Fin q → ℕ) (hHs : ∀ i j, H i j = H j i) (hHr : ∀ i, ∑ j, H i j = h)
    {β : ℝ} (hβ : 1 ≤ β) (hslope : 1728 * β / (2 * (k : ℝ)) ≤ 1/2)
    (s : ℕ) :
    ∃ c : Fin (q^s) → Fin (q^s) → ℕ,
      (∀ i j, c i j = c j i) ∧ (∀ i, ∑ j, c i j = 2*h) ∧
      ∀ (Y : Type u) [PseudoMetricSpace Y] [CompleteSpace Y], HasCATZeroSegments Y →
        Bound (transition H h) Y β → Bound (transition c (2*h)) Y (3480*β) := by
  classical
  have hβ' : 0 ≤ β := by linarith
  have hcap : 2*(6+18*(48*(1+(3480*β)/(2*(k:ℝ)))))*β ≤ 3480*β := calc
    _ = 1740*β + (1728*β/(2*(k:ℝ)))*(3480*β) := by ring
    _ ≤ 1740*β + (1/2)*(3480*β) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hslope (show 0 ≤ 3480*β by positivity))
    _ = _ := by ring
  induction s with
  | zero =>
    refine ⟨fun _ _ => 2*h, fun _ _ => rfl, fun _ => ?_, ?_⟩
    · rw [sum_const, card_univ, Fintype.card_fin, pow_zero, one_smul]
    · intro Y _ _ _ _ x
      have eq (i j : Fin (q^0)) : i = j := Fin.ext (by
        have hi := i.isLt
        have hj := j.isLt
        simp only [pow_zero] at hi hj
        omega)
      have dz (i j : Fin (q^0)) : dist (x i) (x j) = 0 := by rw [eq i j, dist_self]
      have hv : variance x = 0 := calc
        _ = avg (fun _ : Fin (q^0) => avg (fun _ : Fin (q^0) => (0 : ℝ))) :=
          avg_congr _ _ fun i => avg_congr _ _ fun j => by rw [dz i j]; norm_num
        _ = 0 := by simp [avg]
      rw [hv]
      exact mul_nonneg (by positivity) (energy_transition_nonneg _ _ _)
  | succ n ih =>
    let : NeZero (q^n) := ⟨pow_ne_zero _ hq.ne'⟩
    obtain ⟨c, hs, hr, old⟩ := ih
    have hdiv : (2*k) * (2*(2*h))^(2*k) ∣ q := by convert hd using 2; ring
    obtain ⟨g, hgs, hgr, next⟩ := exists_cesaro_cloud_step.{u} (by omega) hh hk hq
      hdiv c hs hr H hHs hHr
    let e : Fin (q^(n+1)) ≃ Fin (q^n) × Fin q := Fintype.equivOfCardEq (by simp [pow_succ])
    refine ⟨fun i j => g (e i) (e j), fun i j => hgs .., ?_, ?_⟩
    · intro i
      exact (e.sum_comp (g (e i))).trans (hgr (e i))
    · intro Y _ _ geom inner
      apply Bound.transition_reindex e g
      intro x
      have hb := next Y geom hβ (show 0 ≤ 3480*β by positivity) inner (old Y geom inner) x
      exact hb.trans (mul_le_mul_of_nonneg_right hcap (energy_transition_nonneg g _ x))

end ThreeFlat.Expander

end OAI
