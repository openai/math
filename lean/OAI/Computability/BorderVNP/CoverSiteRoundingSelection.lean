import OAI.Computability.BorderVNP.CoverSiteFiniteMotions
import OAI.Computability.BorderVNP.ShortenEpochConcentration

/-!
# Choosing the final rounding motion of an epoch

The motion list is chosen using only the fixed finite set of lengths. For
any later pack, a joint choice of one listed motion per factor has rounded
nonlocal bit count bounded by a host constant times total charged length.
Zero-length segments contribute no failures, and all wires use the same
joint motion.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Finset BorderVNP.Cover.Frame

/-- The failure of simultaneous site rounding on the product surface. -/
noncomputable def productRoundingFailure {q : ℕ} (d : ℕ) (x y : Fin q → Surface (d+1)) : ℝ := by
  classical
  exact if (fun i => roundedSite d (x i)) = (fun i => roundedSite d (y i)) then 0 else 1

private theorem product_failure_le {q : ℕ} (d : ℕ) (x y : Fin q → Surface (d+1)) :
    productRoundingFailure d x y ≤ ∑ i, roundingFailure d (x i) (y i) := by
  classical
  have hnon (i : Fin q) : 0 ≤ roundingFailure d (x i) (y i) := by
    unfold roundingFailure; split <;> norm_num
  unfold productRoundingFailure
  split_ifs with h
  · exact sum_nonneg fun i _ => hnon i
  · obtain ⟨i,hi⟩ : ∃ i, roundedSite d (x i) ≠ roundedSite d (y i) := by
      by_contra! hall
      exact h (funext hall)
    have hb := single_le_sum (fun k _ => hnon k) (mem_univ i)
    simpa [roundingFailure,hi] using hb

/-- A table chosen before the input network bounds the nonlocal charged width after
rounding. One selected product motion is applied to every endpoint of every wire. -/
theorem exists_rounding_choice : ∃ C ≥ (0:ℝ), ∀ {L : Type} [Fintype L] (r : L → ℝ),
    (∀ l, 0 ≤ r l) → (∀ l, 4*r l ≤ 1) →
    ∃ (a m : ℕ) (u : Fin m → SL) (hclear : ∀ i, Clears (u i) a),
      ∀ {W : Type*} [Fintype W] (q d : ℕ) (lengthClass : W → L) (width : W → ℝ),
        (∀ j, 0 ≤ width j) →
        ∀ x y : W → Fin q → Surface (d+1+2*a),
        (∀ j k, dist (x j k) (y j k) ≤ r (lengthClass j)) →
        ∃ σ : Fin q → Fin m,
          (∑ j, width j * productRoundingFailure d
            (fun k => surfaceMotion (hclear (σ k)) (d+1) (x j k))
            (fun k => surfaceMotion (hclear (σ k)) (d+1) (y j k))) ≤
          q*C * ∑ j, width j * r (lengthClass j) := by
  classical
  obtain ⟨C,hC,table⟩ := finite_rounding_motions
  refine ⟨C,hC,?_⟩
  intro L _ r hr hsmall
  let Pos := {l : L // 0 < r l}
  obtain ⟨a,m,w,u,hclear,hw,hw1,law⟩ := table (fun l : Pos => r l.val)
    (fun l => l.property) (fun l => hsmall l.val)
  refine ⟨a,m,u,hclear,?_⟩
  intro W _ q d lengthClass width hwid x y hdist
  let p (i : Fin m) : ℝ := w i
  have hp (i : Fin m) : 0 ≤ p i := by unfold p; exact_mod_cast (hw i).le
  have hp1 : ∑ i, p i = 1 := by unfold p; exact_mod_cast hw1
  let prob (σ : Fin q → Fin m) : ℝ := ∏ k, p (σ k)
  have hpσ (σ : Fin q → Fin m) : 0 ≤ prob σ := prod_nonneg fun k _ => hp _
  have htotal : ∑ σ, prob σ = 1 := by
    simp [prob, ← Fintype.prod_sum, hp1]
  let X (j : W) (k : Fin q) (i : Fin m) := surfaceMotion (hclear i) (d+1) (x j k)
  let Y (j : W) (k : Fin q) (i : Fin m) := surfaceMotion (hclear i) (d+1) (y j k)
  let F (j : W) (k : Fin q) (i : Fin m) := roundingFailure d (X j k i) (Y j k i)
  let U (j : W) (σ : Fin q → Fin m) :=
    productRoundingFailure d (fun k => X j k (σ k)) (fun k => Y j k (σ k))
  have hfactor (j : W) (k : Fin q) : ∑ i, p i * F j k i ≤ C*r (lengthClass j) := by
    by_cases h : r (lengthClass j) = 0
    · have he : x j k = y j k := dist_le_zero.mp (h ▸ hdist j k)
      simp [F,X,Y,roundingFailure,he,h]
    · exact law ⟨_,(hr _).lt_of_ne' h⟩ d (x j k) (y j k) (hdist j k)
  have hwire (j : W) : ∑ σ, prob σ * U j σ ≤ (q:ℝ)*C*r (lengthClass j) := by
    calc
      _ ≤ ∑ σ, prob σ * ∑ k, F j k (σ k) :=
        sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (product_failure_le _ _ _) (hpσ σ)
      _ = ∑ k, ∑ i, p i * F j k i := by
        simp_rw [mul_sum]; rw [sum_comm]; apply sum_congr rfl
        intro k _
        exact Epoch.single_moment (fun (_ : Fin q) => p) (fun _ => hp1) k (F j k)
      _ ≤ ∑ _ : Fin q, C*r (lengthClass j) := sum_le_sum fun k _ => hfactor j k
      _ = _ := by simp [mul_assoc]
  let cost (σ : Fin q → Fin m) := ∑ j, width j * U j σ
  obtain ⟨σ,_,hσ⟩ := Epoch.exists_le_weighted prob cost hpσ htotal
  refine ⟨σ,hσ.trans ?_⟩
  calc
    _ = ∑ j, width j * ∑ τ, prob τ * U j τ := by
      simp_rw [cost,mul_sum]; rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro τ _
      ring
    _ ≤ ∑ j, width j * ((q:ℝ)*C*r (lengthClass j)) :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hwire j) (hwid j)
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro j _; ring

end Cover

end BorderVNP
end Computability
end OAI
