import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Computability.DepthThree.MultiTapeMachine
import OAI.Computability.VPVNP.RegularArcGraph
import OAI.Computability.VPVNP.WireGeodesic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The variable-count hypothesis and the characteristic-zero alternative -/

namespace OAI.Computability.MultitapeWeakETH

open OAI.DepthThreeLowerBound OAI.Algorithms.SubexponentialSAT
open VPVNP.SpectralGeometry VPVNP.WireGeometry

def PowerSavingDecision (answer : ∀ v, SAT.CNF (Fin v) → Bool) : Prop :=
  ∃ (η : ℝ) (C d : ℕ) (M : FiniteMultiTapeMachine), 0 < η ∧ η < 1 ∧
    ∀ v (formula : SAT.CNF (Fin v)), SAT.WidthAtMost 3 formula →
      ∃ t : ℕ, MultiTapeHaltsIn M (Encoding.encodeCNF formula) (answer v formula) t ∧
        (t : ℝ) ≤ (2 : ℝ) ^ (C * (v : ℝ) ^ (1 - η)) *
          (1 + v + (Encoding.encodeCNF formula).length : ℕ) ^ d

noncomputable def satAnswer (v : ℕ) (formula : SAT.CNF (Fin v)) : Bool := by
  classical exact decide (SAT.Satisfiable formula)

def WeakETH : Prop := ¬ PowerSavingDecision satAnswer

/-- Port over the algebraic closure of the prime field in characteristic zero.
The arc sum and ordered independent-pair sum are cross-multiplied. -/
def PortZero : Prop := ∃ (D : ℕ) (Γ : ℝ), 0 < D ∧ 0 < Γ ∧
  ∀ minimum : ℕ, ∃ exponent : ℕ, minimum ≤ 2 ^ exponent ∧
    ∃ graph : RegularArcGraph (Fin (2^exponent)) D,
      (∀ u v, Relation.ReflTransGen (fun a b => 0 < graph.multiplicity a b) u v) ∧
      ∀ (X : Type) [MetricSpace X] [CompleteSpace X], HasFractions X →
        RealizableConfigurations (AlgebraicClosure ℚ) X → ∀ place : Fin (2^exponent) → X,
          (D : ℝ) * (∑ u, ∑ v, dist (place u) (place v) ^ 2) ≤
            Γ * (2 : ℝ)^exponent *
              ∑ u, ∑ port : Fin D, dist (place u) (place (graph.reverse (u, port)).1) ^ 2

def PriceZero : Prop := ¬ PortZero

/-- The decision consequence needed from Middle, Theorem 3.2, after taking
width three, setting all weights to one and testing the exact count for positivity. -/
def MiddleCountBridge : Prop :=
  PortZero → PowerSavingDecision (fun _ formula => decide (0 < SAT.count formula))

theorem price_of_weakETH (middle : MiddleCountBridge) (weak : WeakETH) : PriceZero := by
  intro port
  apply weak
  have equal : satAnswer = (fun _ formula => decide (0 < SAT.count formula)) := by
    funext v formula
    apply Bool.eq_iff_iff.mpr
    simp [satAnswer, SAT.count_pos_iff]
  rw [equal]
  exact middle port

end OAI.Computability.MultitapeWeakETH
