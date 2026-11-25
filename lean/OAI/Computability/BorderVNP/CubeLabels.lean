import OAI.Computability.BorderVNP.CubeBalancing

/-!
# Balancing all ordered cable counts and incoming data counts

Lemma 8.2 obtains one common labeling by bounding the sum of squared deviations
from the uniform means. This module gives the finite quantitative statement,
including the `u = v` cable counts, with an explicit numerical sufficient condition.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Balancing

open scoped BigOperators
open Finset

variable {C L E A : Type*} [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Nonempty L]
  [Fintype E] [Fintype A]

/-- The two endpoint prescriptions for one oriented cable bit. -/
def cable (src dst : E → C) (u v : L) (e : E) : Pattern C L :=
  ⟨{src e, dst e}, fun c ↦ if c = src e then u else v⟩

/-- The label required at the receiving cell of a single data bit. -/
def datum (recv : A → C) (u : L) (b : A) : Pattern C L := ⟨{recv b}, fun _ ↦ u⟩

/-- The sum of squared deviations over all ordered cable bins and incoming data bins. -/
noncomputable def deviation (src dst : E → C) (recv : A → C) (x : C → L) : ℝ :=
  (∑ p : L × L, (load (cable src dst p.1 p.2) x -
    Fintype.card E/(Fintype.card L : ℝ)^2)^2) +
    ∑ u : L, (load (datum recv u) x - Fintype.card A/(Fintype.card L : ℝ))^2

/-- Any labeling whose total deviation is at most the uniform mean meets all bin bounds. -/
theorem balanced_of_le_mean (src dst : E → C) (recv : A → C) (W : ℝ) (M : ℕ)
    (hne : ∀ e, src e ≠ dst e)
    (hcable : (Fintype.card E : ℝ) ≤ 2*W) (hdata : (Fintype.card A : ℝ) ≤ W)
    (hE : ∀ c, (univ.filter (fun e ↦ c ∈ ({src e,dst e} : Finset C))).card ≤ M)
    (hA : ∀ c, (univ.filter (fun b ↦ c = recv b)).card ≤ M)
    (hbudget : (Fintype.card L : ℝ)^2 * (4*W*M) + Fintype.card L * (W*M) ≤
      (W / (Fintype.card L : ℝ)^2)^2) (x : C → L)
    (hchoice : deviation src dst recv x ≤ 𝔼 y : C → L, deviation src dst recv y) :
      (∀ u v, load (cable src dst u v) x ≤ 4*W/(Fintype.card L : ℝ)^2) ∧
      (∀ u, load (datum recv u) x ≤ 4*W/Fintype.card L) := by
  classical
  let Z : ℝ := Fintype.card L
  have hZ : 1 ≤ Z := by
    change (1 : ℝ) ≤ Fintype.card L
    exact_mod_cast (show 1 ≤ Fintype.card L from Fintype.card_pos)
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hW : 0 ≤ W := (Nat.cast_nonneg _).trans hdata
  let μ := (Fintype.card E : ℝ) / Z^2
  let ν := (Fintype.card A : ℝ) / Z
  let cvar (p : L × L) (x : C → L) := (load (cable src dst p.1 p.2) x - μ)^2
  let dvar (u : L) (x : C → L) := (load (datum recv u) x - ν)^2
  have hcp (u v : L) : (∑ e : E, chance (cable src dst u v e)) = μ := by
    simp [chance, cable, Finset.card_pair (hne _), μ, Z, div_eq_mul_inv, inv_pow]
  have hdp (u : L) : (∑ b : A, chance (datum recv u b)) = ν := by
    simp [chance, datum, ν, Z, div_eq_mul_inv]
  have cableBound (p : L × L) : (𝔼 x, cvar p x) ≤ 4*W*M := by
    have h := variance_le_incidence (cable src dst p.1 p.2) 2 M
      (fun e ↦ (Finset.card_pair (hne e)).le) hE
    rw [hcp] at h
    change (𝔼 x, cvar p x) ≤ _
    apply h.trans
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_right hcable (Nat.cast_nonneg M)]
  have dataBound (u : L) : (𝔼 x, dvar u x) ≤ W*M := by
    have h := variance_le_incidence (datum recv u) 1 M (by simp [datum])
      (fun c ↦ by simpa only [datum, Finset.mem_singleton] using hA c)
    rw [hdp] at h
    exact h.trans (by simpa using mul_le_mul_of_nonneg_right hdata (Nat.cast_nonneg M))
  let dev (x : C → L) := (∑ p : L × L, cvar p x) + ∑ u : L, dvar u x
  have meanBound : (𝔼 x, dev x) ≤ (W / Z^2)^2 := by
    unfold dev
    rw [Finset.expect_add_distrib, Finset.expect_sum_comm, Finset.expect_sum_comm]
    apply (add_le_add (sum_le_sum fun p _ ↦ cableBound p) (sum_le_sum fun u _ ↦ dataBound u)).trans
    simpa [Z, sq, mul_assoc] using hbudget
  have hx : dev x ≤ (W / Z^2)^2 := hchoice.trans meanBound
  have cnon p : 0 ≤ cvar p x := sq_nonneg _
  have dnon u : 0 ≤ dvar u x := sq_nonneg _
  have csum := Finset.sum_nonneg (s := univ) fun i _ ↦ cnon i
  have dsum := Finset.sum_nonneg (s := univ) fun i _ ↦ dnon i
  have slack : 0 ≤ W/Z^2 := div_nonneg hW (sq_nonneg _)
  have one (z m : ℝ) (h : (z-m)^2 ≤ (W/Z^2)^2) : z ≤ m + W/Z^2 := by
    have ha : |z-m| ≤ W/Z^2 := (sq_le_sq₀ (abs_nonneg _) slack).mp (by simpa using h)
    linarith only [(le_abs_self _).trans ha]
  have hzle : W/Z^2 ≤ W/Z :=
    div_le_div_of_nonneg_left hW hZpos (by nlinarith only [sq_nonneg (Z-1), hZ])
  refine ⟨fun u v ↦ ?_, fun u ↦ ?_⟩
  · have hb := Finset.single_le_sum (fun p _ ↦ cnon p) (Finset.mem_univ (u,v))
    have hs : cvar (u,v) x ≤ (W/Z^2)^2 := (hb.trans (le_add_of_nonneg_right dsum)).trans hx
    have hm := div_le_div_of_nonneg_right hcable (sq_nonneg Z)
    change _ ≤ 4*W/Z^2
    have hl := one _ μ hs
    dsimp only [μ] at hl
    rw [mul_div_assoc] at hm ⊢
    linarith only [hl, hm, slack]
  · have hb := Finset.single_le_sum (fun j _ ↦ dnon j) (Finset.mem_univ u)
    have hs : dvar u x ≤ (W/Z^2)^2 := (hb.trans (le_add_of_nonneg_left csum)).trans hx
    have hm := div_le_div_of_nonneg_right hdata hZpos.le
    change _ ≤ 4*W/Z
    have hl := one _ ν hs
    dsimp only [ν] at hl
    rw [mul_div_assoc]
    linarith only [hl, hm, hzle, div_nonneg hW hZpos.le]

/-- One common labeling meets all the cable and incoming-data bounds. The final
numeric hypothesis states that the second-moment estimate fits within the squared
slack `(W/Z²)²`, where `Z` is the number of labels. -/
theorem exists_balanced_labels (src dst : E → C) (recv : A → C) (W : ℝ) (M : ℕ)
    (hne : ∀ e, src e ≠ dst e)
    (hcable : (Fintype.card E : ℝ) ≤ 2*W) (hdata : (Fintype.card A : ℝ) ≤ W)
    (hE : ∀ c, (univ.filter (fun e ↦ c ∈ ({src e,dst e} : Finset C))).card ≤ M)
    (hA : ∀ c, (univ.filter (fun b ↦ c = recv b)).card ≤ M)
    (hbudget : (Fintype.card L : ℝ)^2 * (4*W*M) + Fintype.card L * (W*M) ≤
      (W / (Fintype.card L : ℝ)^2)^2) :
    ∃ x : C → L,
      (∀ u v, load (cable src dst u v) x ≤ 4*W/(Fintype.card L : ℝ)^2) ∧
      (∀ u, load (datum recv u) x ≤ 4*W/Fintype.card L) := by
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_expect_le (f := deviation (L := L) src dst recv)
    univ_nonempty le_rfl
  exact ⟨x, balanced_of_le_mean src dst recv W M hne hcable hdata hE hA hbudget x hx⟩

end Cube.Balancing

end BorderVNP
end Computability
end OAI
