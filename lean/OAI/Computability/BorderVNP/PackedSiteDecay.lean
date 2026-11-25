import OAI.Computability.BorderVNP.PackedSiteEpochs
import OAI.Computability.BorderVNP.PackedPotential

/-!
# Physical cable width at the last epoch

The potential of a site-routed pack counts its actual nonlocal bits together
with its weighted endpoint concentration. Applying the recurrence to each
dependent selected history gives the uniform exterior budget at the depth
chosen from the team size.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PhysicalEpochs.Factory

open Shortening Shortening.Adaptive Cover Epoch Filter TeamScales Finset
open scoped Classical
attribute [local instance] Epoch.Round.portFintype

variable {D : ℕ} {K : Type*} [Field K] (F : Factory D K)
variable {P : Type} [Fintype P] {bits : P → ℕ} {start T : ℕ}
variable (deep : F.floor + 1 + F.drop*T ≤ start)

include deep in
private theorem volume_le {t : ℕ} (ht : t ≤ T) :
    CoverScale.sites (Cube D) (F.depth start t) ≤ CoverScale.sites (Cube D) start := by
  have hmul := Nat.mul_le_mul_left F.drop ht
  have hs : 1 ≤ F.depth start t := by
    unfold depth
    omega
  let d := F.depth start t
  have hadd : d + F.drop*t = start := by dsimp [d,depth]; omega
  conv_rhs => rw [← hadd,CoverScale.sites_add _ hs]
  apply Nat.le_mul_of_pos_left
  exact pow_pos (zero_lt_one.trans (CoverScale.one_lt_factor _)) _

set_option maxHeartbeats 1200000 in
/-- Dividing by the number of original copies allows the same scalar
recurrence to dominate every physical branch, including the incidence
contribution to its potential. The copy count at the bottom is independent
of the representation of the bottom external slots. -/
theorem normalized_bound {b : ℕ} (hb : 0 < b) (bottom : F.State bits start 0)
    (I : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hbase : bottom.route.potential F.weight / b ≤ I 0)
    (hvol : F.E * CoverScale.sites (Cube D) start ≤ A)
    (hstep : ∀ t < T, I t / 2 + A ≤ I (t+1)) (t : ℕ)
    (q : (F.histories deep bottom t).Index) :
    ((F.histories deep bottom t).term q).route.potential F.weight / ((b : ℝ) * F.fan^t) ≤ I t := by
  let count (t : ℕ) : ℝ := b * (F.fan : ℝ)^t
  have hk : 0 < F.k := by have := F.k_two; omega
  have hfan : 0 < F.fan := pow_pos hk _
  have hc t : 1 ≤ count t :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hb)
      (one_le_pow₀ (by exact_mod_cast hfan))
  apply (div_le_iff₀ (zero_lt_one.trans_le (hc t))).mpr
  refine history_induction bottom (F.epoch deep) (fun n p => p.route.potential F.weight ≤ I n * count n) ?_ ?_ t q
  · simpa [count] using (div_le_iff₀ (show 0 < (b : ℝ) by exact_mod_cast hb)).mp hbase
  intro n child hchild
  by_cases ht : n < T
  · let H := F.output deep ht child
    let Z : ProfileSum (F.State bits start (n+1)) :=
      ⟨Fin H.terms,inferInstance,fun j => ⟨H.pack j,reindexRoutes (F.levels deep ht).2.1 (H.routes j)⟩⟩
    rw [show F.epoch deep n child = Z from dite_eq_left ht]
    intro j
    change (reindexRoutes _ (H.routes j)).potential F.weight ≤ _
    rw [reindexRoutes_potential]
    have he := H.bound j
    have hmax : maximumLeaf hk id
        (fun i => (reindexRoutes (F.levels deep ht).2.2.symm (child i).route).potential F.weight) ≤ I n * count n := by
      apply sup'_le
      intro i _
      exact (reindexRoutes_potential _ _ _).le.trans (hchild i)
    have hv (tiles : Fintype (Cube D → Deck (F.depth start (n+1)-1+1+F.drop+1))) :
        F.E * (@Fintype.card _ tiles : ℝ) ≤ A := by
      rw [card_eq_sites (Cube D) _ tiles]
      rw [(F.levels deep ht).2.2]
      apply le_trans _ hvol
      apply mul_le_mul_of_nonneg_left _ F.E_pos.le
      exact_mod_cast F.volume_le deep ht.le
    have hden : (F.k : ℝ)^F.stages = (F.fan : ℝ) := (Nat.cast_pow F.k F.stages).symm
    have hcst := le_mul_of_one_le_right hA (hc n)
    have hn := mul_le_mul_of_nonneg_right (hstep n ht) (zero_lt_one.trans_le (hc n)).le
    have hy : (H.routes j).potential F.weight / (F.fan : ℝ) ≤ I (n+1)*count n := by
      rw [← hden]
      apply he.trans
      apply (add_le_add (div_le_div_of_nonneg_right hmax (by norm_num : (0:ℝ) ≤ 2)) (hv _)).trans
      apply (add_le_add_right hcst _).trans
      convert hn using 1; ring
    calc
      _ ≤ (I (n+1)*count n) * (F.fan : ℝ) :=
        (div_le_iff₀ (by exact_mod_cast hfan)).mp hy
      _ = _ := by dsimp [count]; rw [pow_succ]; ring
  · let Z : ProfileSum (F.State bits start (n+1)) := ⟨Empty,inferInstance,Empty.elim⟩
    rw [show F.epoch deep n child = Z from dite_eq_right ht]
    exact fun q => Empty.elim q

private noncomputable def envelope (x A : ℝ) : ℕ → ℝ
  | 0 => x
  | t+1 => envelope x A t / 2 + A

/-- Little-o of the rounded exterior budget, simultaneously for all physical
histories and all positive batch sizes up to the prescribed stretched
exponential. The initial cost is measured on the very bottom bundle fed to
the first epoch. -/
theorem eventually_nonlocal_width {τ : ℝ} (hτ : 0 < τ) (hτ' : τ < 1/2) (u : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ (C ε : ℝ), 0 ≤ C → 0 < ε →
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2 ^ ((n : ℝ) ^ ω) →
    ∀ {P : Type} [Fintype P] {bits : P → ℕ} {b start : ℕ} (_hb : 0 < b)
      (deep : F.floor + 1 + F.drop * epochs τ n ≤ start)
      (_hv : (CoverScale.sites (Cube D) start : ℝ) ≤ r * (n : ℝ) ^ (9/10 : ℝ))
      (bottom : F.State bits start 0),
      bottom.route.potential F.weight / b ≤ C * volume τ r n * (logWidth r n : ℝ)^u →
      ∀ q : (F.histories deep bottom (epochs τ n)).Index,
        ((F.histories deep bottom (epochs τ n)).term q).route.nonlocalWidth /
          ((b : ℝ) * F.fan ^ epochs τ n) ≤ ε * exterior (τ/5) r n := by
  obtain ⟨ω,hω,h⟩ := eventually_charged_width hτ hτ' u
  refine ⟨ω,hω,?_⟩
  intro C ε hC hε
  filter_upwards [h C F.E ε hC F.E_pos.le hε] with n hn
  intro r hr hr' P _ bits b start hb deep hv bottom hbot q
  let a := F.E * r * (n : ℝ)^(9/10 : ℝ)
  let f := envelope (bottom.route.potential F.weight / b) a
  have hv' : F.E * CoverScale.sites (Cube D) start ≤ a := by
    simpa only [a,mul_assoc] using mul_le_mul_of_nonneg_left hv F.E_pos.le
  have hh := F.normalized_bound deep hb bottom f (show 0 ≤ a by dsimp [a]; exact mul_nonneg (mul_nonneg F.E_pos.le (Nat.cast_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (le_refl _) hv' (fun _ _ => le_refl _) _ q
  have hcost := hn r hr hr' f hbot (fun _ _ => le_refl _)
  apply le_trans _ (hh.trans hcost)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact le_add_of_nonneg_right (mul_nonneg F.weight_pos.le
    ((F.histories deep bottom (epochs τ n)).term q).route.nonneg_width_concentration.2)

end Packing.PhysicalEpochs.Factory

end BorderVNP
end Computability
end OAI
