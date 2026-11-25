import OAI.Computability.BorderVNP.CrossingFusionProjection
import OAI.Computability.BorderVNP.CrossingFusionBudget
import OAI.Computability.BorderVNP.CrossingStageChecker
import OAI.Computability.BorderVNP.CrossingFromApproximation

/-!
# The all-length signed side projections in Section 4.3

Use one polynomial in `q = 2^m` for the source length needed to check all the paths and
output variables of an oriented side. Choosing `m = ⌊c₁ log₂ n⌋` with a single absolute
`c₁ > 0` makes that length available at every sufficiently large `n`. The two extra bridge
ports accommodate rounding each binary field separately. All the chosen states, layouts
and Boolean checkers are independent of the coefficient field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

universe u

open Filter VPVNP
open FusionStage

private noncomputable def localCheckers {m D : ℕ} (w : WireStates (leastEnergy m) (2^m))
    (left : Bool) (o : Fin D → Bool) : Checkers w left o := fun i =>
  checker w (i.val*leastEnergy m) (!(o i.rev)) (if o i.rev then left else !left)

/-- Every orientation of either side is a variable-or-scalar specialization over any
coefficient ring once the source has room for the weighted Boolean verifier. -/
theorem side_projection_at_sourceCap {n m D p : ℕ} (w : WireStates (leastEnergy m) (2^m))
    (addr : CutBit D (2*leastEnergy m) (stateCountAt (D*leastEnergy m)) ↪ Fin p × Fin m)
    (left : Bool) (o : Fin D → Bool) (hD : D ≤ m) (hp : p ≤ 2^m) (hH : 2*leastEnergy m ≤ 2^m)
    (hn : sourceCap (2^m) ≤ n) (R : Type u) [CommRing R] :
    ∃ φ : Projection R (Fin n × Bool) ((Fin D ⊕ Fin p) × Fin (2^m)),
      φ.hom (MvPolynomial.map (Int.castRingHom R) (Pstar n)) =
        sidePolynomial (binarySideTensor R w addr left o) := by
  let B := checkerCap (2^m)
  let f := localCheckers w left o
  obtain ⟨F⟩ := exists_fullFrame f addr
  have hlocal (i : Fin D) : (f i).guesses ≤ B ∧ (f i).frame.size ≤ B :=
    checker_stage_budget w (i.val*leastEnergy m) _ _ hD Nat.lt_two_pow_self.le hH
      (Nat.mul_le_mul_right _ i.isLt.le)
  obtain ⟨hr, ht', hs⟩ := side_resources f addr hD hp hH hlocal F.size_le
  have ht : Fintype.card (Labels D p m) ≤ fullCap B := by
    simpa only [Labels, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Nat.add_comm ((D+p)*2^m) D] using ht'
  exact projection_at_length R f addr F (fullCap B) n hr ht hs hn

/-- Concrete signed side projections at a fixed length, including the complete Boolean
frame, the weighted-CNF projection and all gate, label and certificate budgets. -/
theorem binarySideProjections_at_sourceCap {n m D : ℕ} (hm : 0 < m) (hD : D ≤ m)
    (hp : bridgePorts m D + 2 ≤ 2^m) (hH : 2*leastEnergy m ≤ 2^m)
    (hn : sourceCap (2^m) ≤ n) (K : Type u) [Field K] : HasBinarySideProjections K n m D := by
  obtain ⟨w⟩ := exists_wireStates (leastEnergy m) (2^m) (leastEnergy_spec m).1 (leastEnergy_spec m).2
  let addr := cutBitAddress (binary_capacity hm hD)
  exact ⟨w, addr, fun o => side_projection_at_sourceCap w addr true o hD hp hH hn K⟩

/-- One absolute choice of the logarithmic bit width works for every fixed direction
constant, every sufficiently large source length and all fields. -/
theorem exists_width_binarySideProjections :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∀ c₀ : ℝ, 0 < c₀ → ∀ᶠ n : ℕ in atTop,
      ∀ (K : Type u) [Field K], HasBinarySideProjections K n (width c₁ n) (directions c₀ (width c₁ n)) := by
  obtain ⟨c₁, hc₁, hc₁', hfit⟩ := fits_source_length_of_polynomial
    (bits := fun m => sourceCap (2^m)) sourceCap_polynomial (Filter.Eventually.of_forall fun _ => le_rfl)
  refine ⟨c₁, hc₁, hc₁', ?_⟩
  intro c₀ hc₀
  filter_upwards [hfit, (tendsto_width hc₁).eventually eventually_initial_table_le,
    eventual_layout_dimensions hc₀ hc₁ hc₁'] with n hn hH hd
  let m := width c₁ n
  let D := directions c₀ m
  let p := bridgePorts m D + 2
  obtain ⟨hm, hlarge, hD, hp, _, _, _⟩ := hd
  change 441 ≤ D at hlarge
  change (p : ℝ) ≤ 21/20 * Real.sqrt D at hp
  have hroot : 21 ≤ Real.sqrt D := Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hlarge)
  have hpd : p ≤ D := by
    apply (Nat.cast_le (α := ℝ)).mp
    calc
      _ ≤ 21/20 * Real.sqrt D := hp
      _ ≤ Real.sqrt D * Real.sqrt D := mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
  intro K _
  exact binarySideProjections_at_sourceCap hm hD ((hpd.trans hD).trans Nat.lt_two_pow_self.le) hH.2 hn K

/-- An approximation at the common length now produces the paid antipodal identity without
any assumption of side-program availability. -/
theorem exists_width_paidIdentity_of_small_approximation :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∀ c₀ : ℝ, 0 < c₀ → 6*c₀^2 < 1/500 → ∀ᶠ n : ℕ in atTop,
      let m := width c₁ n
      let D := directions c₀ m
      ∀ (K : Type u) [Field K] (s : ℕ), (s : ℝ) ≤ (2:ℝ)^(1/100 * (m * Real.sqrt D)) →
        geometricApprox n s (MvPolynomial.map (Int.castRingHom K) (Pstar n)) →
        2 ≤ D ∧ ∃ t : ℕ, 0 < t*m ∧ Nonempty (PaidIdentity K D (t*m)) := by
  obtain ⟨c₁, h₁, h₁', hproj⟩ := exists_width_binarySideProjections.{u}
  refine ⟨c₁, h₁, h₁', ?_⟩
  intro c₀ h₀ hsmall
  filter_upwards [hproj c₀ h₀, eventually_paidIdentity_of_small_approximation.{u} h₀ h₁ h₁' hsmall]
    with n hp h
  dsimp only at h ⊢
  intro K inst s hs ha
  exact h K (hp K) s hs ha

end Crossing

end BorderVNP
end Computability
end OAI
