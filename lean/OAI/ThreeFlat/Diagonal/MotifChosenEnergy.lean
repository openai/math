import OAI.ThreeFlat.Diagonal.MotifIntegerChoice
import OAI.ThreeFlat.Diagonal.MotifHistogram

namespace OAI
/-! # Energy of the integer-selected histogram motif

The native grid minimizer uses at most the repetition count supplied by
the geometric rounding lemma. Consequently its shorter selector strings
also meet the same quadratic energy bound.
-/

namespace ThreeFlat.Diagonal.MotifIntegerChoice

open Computability.VPVNP.MotifGrid Computability.VPVNP.MotifWidths MotifOuterTerms
open scoped Classical BigOperators

variable {E S : Type} [Fintype E] [Fintype S] {p : E → ℝ} {q : S → ℝ} {H R : ℝ}

theorem choose_grid (G : StrictGrids p q H R) (hp : ∀ e, 0<p e) {h t : ℕ} (ht : 0<t) (hh : 0<h)
    (row : G.demands) (rows : List G.demands) (covers : ∀ z, z∈row::rows) (b : E → ℕ) :
    let tiles := fun z e => h * G.demandWidths t z e
    let z := best (score b tiles) row rows
    let r := score b tiles z
    r ≤ copies (widthNorm p (fun e => b e)) (h*(t*G.denominator)) ∧ ∀ e, b e ≤ tiles z e * r := by
  obtain ⟨z,hz⟩ := exists_padded_grid G hp t h ht hh b
  exact best_grid b _ row rows z (covers z) _ (fun e => (hz e).trans_eq (Nat.mul_comm ..))

/-- The integer-selected count may be smaller than the geometric count.
Every histogram on this count obeys the same bound, including all-zero
demands and zero-width supply edges. -/
theorem chosen_histogram_energy (hq : ∀ e, 0<q e) {L s : ℕ} (hL : 0<L) {H' : ℝ} (hR : 0≤R)
    (gap : (R+s/(L:ℝ)*widthNorm q (fun _ => 1))^2 < H') :
    ∃ C : ℝ, ∀ N : ℝ, 0≤N → ∀ r ≤ copies N L, ∀ (T : Type) [Fintype T] [DecidableEq T]
      (w : T → S → ℕ), (∀ t, widthNorm q (fun e => (w t e : ℝ)) ≤ (L:ℝ)*R) → ∀ a : Histogram T r,
      widthNorm q (fun e => ((histWidth w a e+r*s : ℕ):ℝ))^2 ≤ H'*N^2+C := by
  obtain ⟨C,hC⟩ := padded_energy_le q hq hL hR gap
  refine ⟨C, ?_⟩
  intro N hN r hr T _ _ w hb a
  have approx : (r : ℝ) ≤ copies N L := by exact_mod_cast hr
  have hn := histogram_norm w q hq hb a
  have upper : widthNorm q (fun e => (histWidth w a e : ℝ)) ≤ (copies N L : ℝ)*L*R := by
    rw [mul_assoc]
    exact hn.trans (mul_le_mul_of_nonneg_right approx (mul_nonneg (Nat.cast_nonneg _) hR))
  apply le_trans _ (hC N (histWidth w a) hN upper)
  apply pow_le_pow_left₀ (Real.sqrt_nonneg _) _ 2
  apply norm_mono _ _ _ hq (fun _ => Nat.cast_nonneg _)
  intro e
  exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_right s hr) (histWidth w a e)

end ThreeFlat.Diagonal.MotifIntegerChoice

end OAI
