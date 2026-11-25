import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The compact additive-state space in Appendix A.1

This file proves the topological reduction to a finite inconsistent system. It
does not assert that this system has a solution: ruling out a finite obstruction
also requires the integer cone certificate and the tensor rank-growth argument.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

open Set

variable {S : Type*} [CommSemiring S] [PartialOrder S]

/-- Normalized additive monotone states with the additional detection inequality.
Multiplicativity is deliberately not included. -/
def stateSet (T : S) (k : ℕ) : Set (S → ℝ) :=
  {f | f 0 = 0 ∧ f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧
    Monotone f ∧ ∀ s, (k : ℝ) * f s ≤ f (T * s)}

/-- Individual conditions, each of which uses only finitely many coordinates. -/
inductive StateConstraint (S : Type*) [CommSemiring S] [PartialOrder S] where
  | zero
  | one
  | add (x y : S)
  | order (x y : S) (h : x ≤ y)
  | detect (s : S)

def StateConstraint.Holds (T : S) (k : ℕ) (f : S → ℝ) :
    StateConstraint S → Prop
  | .zero => f 0 = 0
  | .one => f 1 = 1
  | .add x y => f (x + y) = f x + f y
  | .order x y _ => f x ≤ f y
  | .detect s => (k : ℝ) * f s ≤ f (T * s)

theorem mem_stateSet_iff (T : S) (k : ℕ) (f : S → ℝ) :
    f ∈ stateSet T k ↔ ∀ c : StateConstraint S, c.Holds T k f := by
  constructor
  · rintro ⟨hzero, hone, hadd, hmono, hdetect⟩ c
    cases c with
    | zero => exact hzero
    | one => exact hone
    | add x y => exact hadd x y
    | order x y h => exact hmono h
    | detect s => exact hdetect s
  · intro h
    exact ⟨h .zero, h .one, fun x y => h (.add x y),
      fun _ _ hxy => h (.order _ _ hxy), fun s => h (.detect s)⟩

theorem StateConstraint.isClosed (T : S) (k : ℕ) (c : StateConstraint S) :
    IsClosed {f : S → ℝ | c.Holds T k f} := by
  cases c with
  | zero => exact isClosed_eq (continuous_apply 0) continuous_const
  | one => exact isClosed_eq (continuous_apply 1) continuous_const
  | add x y =>
    exact isClosed_eq (continuous_apply (x + y))
      ((continuous_apply x).add (continuous_apply y))
  | order x y _ => exact isClosed_le (continuous_apply x) (continuous_apply y)
  | detect s =>
    exact isClosed_le (continuous_const.mul (continuous_apply s))
      (continuous_apply (T * s))

theorem stateSet_isClosed (T : S) (k : ℕ) : IsClosed (stateSet T k) := by
  have heq : stateSet T k = ⋂ c : StateConstraint S, {f | c.Holds T k f} := by
    ext f
    simp only [mem_iInter, mem_ofPred_eq, mem_stateSet_iff]
  rw [heq]
  exact isClosed_iInter fun c => c.isClosed T k

theorem state_natCast {T : S} {k : ℕ} {f : S → ℝ}
    (hf : f ∈ stateSet T k) (n : ℕ) : f (n : S) = (n : ℝ) := by
  induction n with
  | zero => simpa only [Nat.cast_zero] using hf.1
  | succ n ih =>
    rw [Nat.cast_succ, hf.2.2.1, ih, hf.2.1, Nat.cast_succ]

/-- The coordinate box uses ordinary rank only as a finite upper bound. -/
def coordinateBox (R : S → ℕ) : Set (S → ℝ) :=
  {f | ∀ s, f s ∈ Icc 0 (R s : ℝ)}

omit [CommSemiring S] [PartialOrder S] in
theorem coordinateBox_isCompact (R : S → ℕ) : IsCompact (coordinateBox R) :=
  isCompact_pi_infinite fun _ => isCompact_Icc

theorem stateSet_subset_coordinateBox (T : S) (k : ℕ) (R : S → ℕ)
    (hzero : ∀ s : S, 0 ≤ s) (hR : ∀ s : S, s ≤ (R s : S)) :
    stateSet T k ⊆ coordinateBox R := by
  intro f hf s
  constructor
  · simpa only [hf.1] using hf.2.2.2.1 (hzero s)
  · simpa only [state_natCast hf] using hf.2.2.2.1 (hR s)

theorem stateSet_isCompact (T : S) (k : ℕ) (R : S → ℕ)
    (hzero : ∀ s : S, 0 ≤ s) (hR : ∀ s : S, s ≤ (R s : S)) :
    IsCompact (stateSet T k) :=
  (coordinateBox_isCompact R).of_isClosed_subset (stateSet_isClosed T k)
    (stateSet_subset_coordinateBox T k R hzero hR)

theorem stateSet_convex (T : S) (k : ℕ) : Convex ℝ (stateSet T k) := by
  intro f hf g hg a b ha hb hab
  change a * f 0 + b * g 0 = 0 ∧ a * f 1 + b * g 1 = 1 ∧
    (∀ x y, a * f (x + y) + b * g (x + y) =
      (a * f x + b * g x) + (a * f y + b * g y)) ∧
    Monotone (fun x => a * f x + b * g x) ∧
    ∀ s, (k : ℝ) * (a * f s + b * g s) ≤
      a * f (T * s) + b * g (T * s)
  refine ⟨by rw [hf.1, hg.1]; ring, by simpa [hf.2.1, hg.2.1] using hab, ?_, ?_, ?_⟩
  · intro x y
    rw [hf.2.2.1, hg.2.2.1]
    ring
  · intro x y hxy
    exact add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.1 hxy) ha)
      (mul_le_mul_of_nonneg_left (hg.2.2.2.1 hxy) hb)
  · intro s
    have h := add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.2 s) ha)
      (mul_le_mul_of_nonneg_left (hg.2.2.2.2 s) hb)
    nlinarith

/-- Compactness gives an actual finite subsystem when no state exists. -/
theorem finite_inconsistent_subsystem (T : S) (k : ℕ) (R : S → ℕ)
    (hnone : stateSet T k = ∅) :
    ∃ F : Finset (StateConstraint S),
      ¬ ∃ f ∈ coordinateBox R, ∀ c ∈ F, c.Holds T k f := by
  have hempty : (coordinateBox R ∩
      ⋂ c : StateConstraint S, {f | c.Holds T k f}) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro f ⟨_, hf⟩
    have hstate : f ∈ stateSet T k := (mem_stateSet_iff T k f).mpr
      (by simpa only [mem_iInter, mem_ofPred_eq] using hf)
    rw [hnone] at hstate
    exact hstate
  obtain ⟨F, hF⟩ := (coordinateBox_isCompact R).elim_finite_subfamily_closed
    (fun c : StateConstraint S => {f | c.Holds T k f})
    (fun c => c.isClosed T k) (Set.disjoint_iff_inter_eq_empty.mpr hempty)
  refine ⟨F, ?_⟩
  rintro ⟨f, hf, hconstraints⟩
  have hmem : f ∈ coordinateBox R ∩
      ⋂ c ∈ F, {f | c.Holds T k f} :=
    ⟨hf, by simpa only [mem_iInter, mem_ofPred_eq] using hconstraints⟩
  exact Set.disjoint_left.mp hF hmem.1 hmem.2

end OAI.LinearAlgebra.TensorSpectrum
