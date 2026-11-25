import OAI.Computability.NearSquareRoot.PhysicalWalshNodeGuard
import OAI.Computability.NearSquareRoot.PhysicalWalshBaseNorm

/-! # Numerical stability at a terminal recursive Walsh node

The prefix and suffix fields select the physical records in the two-bit leaf.
All spectator copies contribute to the Euclidean norm. A headroom bound on
this finite row establishes the actual recursive guard and identifies the
stored tape records with the rounded arithmetic used by the recursion.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication PhysicalWalshBase SynchronizedPadding KernelPass
noncomputable section

abbrev baseSize (s : Shape) := s.pref * 4 * s.suff

/-- At a terminal node the two active bits leave exactly four slots between
the prefix and suffix spectators. -/
theorem count_base (A : ℕ) (s : Shape) (hl : s.level = 0) : count A s = baseSize s := by
  simp [count, inner, grow, hl, baseSize, Nat.mul_assoc]

def baseValues (p : ℕ) (s : Shape) (x : Data s) : EuclideanSpace ℂ (Fin (baseSize s)) :=
  WithLp.toLp 2 fun t => Grid.meaning p s.w (x t.val)

def baseIsometry (s : Shape) : EuclideanSpace ℂ (Fin (baseSize s)) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (Fin (baseSize s)) :=
  matrixIsometry _ (field_unitary s.pref s.suff)

private theorem fromOrdinal_at (s : Shape) (x : Data s) (t : Fin (baseSize s)) :
    recordAt (fromOrdinal (P := s.pref) (B := s.suff) x) t = x t.val := by
  change x ((t.val/s.suff/4*4+t.val/s.suff%4)*s.suff+t.val%s.suff) = x t.val
  rw [Nat.div_add_mod', Nat.div_add_mod']

private theorem field_base_at (s : Shape) (x : Data s) (t : Fin (baseSize s)) :
    recordAt (applyField (fromOrdinal (P := s.pref) (B := s.suff) x)) t = base s x t.val := rfl

private theorem field_stored_at (s : Shape) (x : Data s) (t : Fin (baseSize s)) :
    recordAt (storedBase (fromOrdinal (P := s.pref) (B := s.suff) x)) t =
      storedAt s.suff x t.val := rfl

/-- The headroom test controls the four accumulators of every spectator pair. -/
theorem baseGuard_of_norm (p : ℕ) (s : Shape) (x : Data s) (M : ℝ)
    (bound : ‖baseValues p s x‖ ≤ M) (room : M*2^p < 2^s.w) : baseGuard s x := by
  apply fitsField_of_norm p (fromOrdinal (P := s.pref) (B := s.suff) x) M _ room
  simpa only [Function.comp_def, fromOrdinal_at, baseValues] using bound

/-- The command returns exactly the recursive evaluator's value on every
physical ordinal, including the first and last spectator groups. -/
theorem storedAt_eq_base (s : Shape) (x : Data s) (fit : baseGuard s x) (t : Fin (baseSize s)) :
    storedAt s.suff x t.val = base s x t.val := by
  rw [← field_stored_at, ← field_base_at]
  exact congrArg (fun z => recordAt z t) (storedBase_eq (fromOrdinal (P := s.pref) (B := s.suff) x) fit)

/-- The local roundoff is charged once per actual tape record, with unitary
propagation of the incoming perturbation. -/
theorem base_error (p : ℕ) (s : Shape) (x : Data s) (ideal : EuclideanSpace ℂ (Fin (baseSize s)))
    (fit : baseGuard s x) :
    ‖baseValues p s (base s x) - baseIsometry s ideal‖ ≤
      Real.sqrt (baseSize s) * (2/(2:ℝ)^p) + ‖baseValues p s x - ideal‖ := by
  have h := field_error p (fromOrdinal (P := s.pref) (B := s.suff) x) fit
  have localBound : ‖baseValues p s (base s x) - baseIsometry s (baseValues p s x)‖ ≤
      Real.sqrt (baseSize s) * (2/(2:ℝ)^p) := by
    simpa only [Function.comp_def, fromOrdinal_at, field_base_at, Fintype.card_fin, baseValues,
      baseIsometry] using h
  have stable : ‖baseIsometry s (baseValues p s x) - baseIsometry s ideal‖ = ‖baseValues p s x - ideal‖ := by
    rw [← map_sub, (baseIsometry s).norm_map]
  exact (norm_sub_le_norm_sub_add_norm_sub _ (baseIsometry s (baseValues p s x)) _).trans
    (add_le_add localBound stable.le)

/-- This establishes `Good` and the Euclidean row error for the actual recursive
entry point when it reaches its two-bit base. -/
theorem run_base_stable {a W : ℕ} (hW : 0 < W) (plan : Plan (a+1) W W) (p : ℕ)
    (s : Shape) (hl : s.level = 0) (x : Data s) (ideal : EuclideanSpace ℂ (Fin (baseSize s)))
    (M : ℝ) (bound : ‖baseValues p s x‖ ≤ M) (room : M*2^p < 2^s.w) :
    Good hW plan s x ∧
      ‖baseValues p s (run hW plan s x) - baseIsometry s ideal‖ ≤
        Real.sqrt (baseSize s) * (2/(2:ℝ)^p) + ‖baseValues p s x - ideal‖ := by
  have fit := baseGuard_of_norm p s x M bound room
  constructor
  · simpa only [Good, hl, goodWith] using fit
  · rw [run_base hW plan s hl]
    exact base_error p s x ideal fit

end
end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
