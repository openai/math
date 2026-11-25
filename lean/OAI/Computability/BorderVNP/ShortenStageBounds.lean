import OAI.Computability.BorderVNP.ShortenRecurrence

/-!
# Uniformizing the coefficients of the finitely many shortening stages

The contraction factor is fixed by the crossing before the number of
rounds is chosen. Each subsequent preparation may enlarge the other
coefficient in (6.3). Summing these nonnegative coefficients after the
rounds have been prepared gives a uniform constant before the fan-in
and starting cover depth are chosen.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Filter Topology Finset

/-- Equation (6.3) on each node, with a separate coefficient for each of
the finitely many prepared relative catalogs. -/
def Batch.StageBounds {k b : ℕ} (T : Batch k) (hk : 0 < k) (r V : ℝ)
    (C : Fin b → ℝ) : Prop :=
  ∀ i : Fin b, ∀ p : T.Packs (i.val + 1),
    let W := (∑ j, T.length (T.child p j)) / k
    let X := univ.sup' ⟨⟨0, hk⟩, mem_univ _⟩ fun j => T.concentration (T.child p j)
    T.length p / k ≤ r * W + C i * (Real.sqrt k)⁻¹ * X + C i * V ∧
    T.concentration p / k ≤ C i * (W + (Real.sqrt k)⁻¹ * X)

/-- Stage-by-stage estimates imply the hypothesis of the envelope iteration
uniformly over the children and all realized profile branches. -/
theorem Batch.estimates_of_stages {k b : ℕ} (T : Batch k) {hk : 0 < k} {r V : ℝ}
    (hV : 0 ≤ V) {C : Fin b → ℝ} (hC : ∀ i, 0 ≤ C i)
    (hpos : ∀ j < b, ∀ p : T.Packs j, 0 ≤ T.length p ∧ 0 ≤ T.concentration p)
    (hstep : T.StageBounds hk r V C) : T.Estimates hk b r (∑ i, C i) V := by
  intro j hj p
  let i : Fin b := ⟨j,hj⟩
  obtain ⟨hw,hx⟩ := hstep i p
  have hc : C i ≤ ∑ i, C i := single_le_sum (f := C) (fun i _ => hC i) (mem_univ _)
  have ht : 0 ≤ (Real.sqrt k)⁻¹ := by positivity
  have ha : 0 ≤ (∑ a, T.length (T.child p a)) / k :=
    div_nonneg (sum_nonneg fun a _ => (hpos _ hj _).1) (Nat.cast_nonneg _)
  let zero : Fin k := ⟨0,hk⟩
  have hm : 0 ≤ univ.sup' ⟨zero, mem_univ _⟩ fun a => T.concentration (T.child p a) :=
    ((hpos _ hj (T.child p zero)).2).trans (le_sup' (fun a => T.concentration (T.child p a)) (mem_univ zero))
  exact ⟨hw.trans (add_le_add (add_le_add_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc ht) hm) _)
    (mul_le_mul_of_nonneg_right hc hV)),
    hx.trans (mul_le_mul_of_nonneg_right hc (add_nonneg ha (mul_nonneg ht hm)))⟩

/-- Finite-stage version of Lemma 6.1's arithmetic. The radius and saving
from the fixed crossing determine a single contraction; the round count
is chosen before all coefficients from the relative catalogs and motions. -/
theorem exists_epoch_of_stage_bounds {ν L A : ℝ} (hν : 0 < ν) (hL : 0 ≤ L) (hA : 0 ≤ A) :
    let r := max 0 (1-(ν/2)/2)
    ∃ b : ℕ, 0 < b ∧ ∀ (C : Fin b → ℝ) (Cin Cout : ℝ),
      (∀ i, 0 ≤ C i) → 0 ≤ Cin → 0 ≤ Cout →
      ∃ weight : ℝ, 0 < weight ∧ ∃ E : ℝ, 0 < E ∧
        ∀ᶠ k : ℕ in atTop, ∃ hk : 0 < k, ∀ (T : Batch k) (M V : ℝ), 0 ≤ M → 0 ≤ V →
          (∀ j < b, ∀ p : T.Packs j, 0 ≤ T.length p ∧ 0 ≤ T.concentration p) →
          T.StageBounds hk r V C →
          (∀ p : T.Packs 0, T.length p ≤ M * L ∧ T.concentration p ≤ M * (Cin / weight)) →
          ∀ p : T.Packs b,
            (A * T.length p + weight * Cout * T.concentration p) / (k : ℝ)^b ≤
              M / 2 + E * V := by
  intro r
  have hr : 0 ≤ r := le_max_left ..
  have hr' : r < 1 := max_lt (by norm_num) (by linarith)
  obtain ⟨b,hb,bound⟩ := exists_shortening_epoch hr hr' hL hA
  refine ⟨b,hb,?_⟩
  intro C Cin Cout hC hin hout
  obtain ⟨weight,hw,E,hE,event⟩ := bound (∑ i, C i) Cin Cout (sum_nonneg fun i _ => hC i) hin hout
  refine ⟨weight,hw,E,hE,?_⟩
  filter_upwards [event] with k h
  obtain ⟨hk,h⟩ := h
  refine ⟨hk,?_⟩
  intro T M V hM hV hpos step input
  exact h T M V hM hV (T.estimates_of_stages hV hC hpos step) input

end Shortening

end BorderVNP
end Computability
end OAI
