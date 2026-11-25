import OAI.Optimization.LinearProgramming.Geometry.LabelTheorem
import OAI.Optimization.LinearProgramming.Geometry.WinningAssignment
import OAI.Optimization.LinearProgramming.Geometry.GeneratorService
import OAI.Optimization.LinearProgramming.Geometry.DimensionBounds
import OAI.Optimization.LinearProgramming.Compression.MinorOrder

/-! The deterministic marked-coordinate decision procedure of Section 2.3, reducing a
rational complementary basis pair to the paper's compression and extremal-sign algorithms. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Submodule Compression PriceGame
open scoped Matrix

variable {n r s : ℕ}

/-- The common assignment specification supplied by the minor compression theorem. -/
def AdmissibleMinorAssignment (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (F : ℕ) (f : NonzeroPairMinor D E → ℚ) : Prop :=
  (∀ u, |(f u : ℝ)| ≤ F) ∧ FourLogAccuracy (geoCutoff n : ℝ) (pairMinorLog D E) (fun u => (f u : ℝ))

/-- A request routine has the on-demand compression guarantees used by the subspace decision.
The proxies and simultaneous completions here are analysis witnesses, never program inputs. -/
def SubspaceRequestCorrect (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (request : MinorRequest (NonzeroPairMinor D E)) (F : ℕ) : Prop :=
  ∃ l : NonzeroPairMinor D E → ℝ,
    (∀ i, |l i - pairMinorLog D E i| ≤ 1 / 2 ^ (100 * (n + 1)^3 + 7 : ℕ)) ∧
    RestartTest l request ∧
    ∀ J : Finset (NonzeroPairMinor D E), IsDissociated l J →
      ∃ f : NonzeroPairMinor D E → ℚ, AdmissibleMinorAssignment D E F f ∧
        ∀ u v, request J u = some v → f u = v

/-- Run the price learner on the one-coordinate geometric query. Only scalar minor values
and labels are computed during execution. The scalar `maxQueries` is supplied directly;
the code never traverses the possible continuations to determine its clock. `none` can occur when the two input routines fail
their budgets; the theorem proves it cannot occur under their specified contracts. -/
def subspaceDecisionRun (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (request : MinorRequest (NonzeroPairMinor D E)) (maxQueries : ℕ) (learner : PriceGame.Tree n) :=
  Recovery.run States.Restart.step
    (generatorService request (fun q : PriceGame.Query n => geometricLabel D E q.prices q.index))
    (maxQueries + 1) learner (minorRestartBudget n + 1) ∅

def subspaceDecision (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (request : MinorRequest (NonzeroPairMinor D E)) (maxQueries : ℕ) (learner : PriceGame.Tree n) : Bool :=
  (subspaceDecisionRun D E request maxQueries learner).value.getD false

/-- From the sign learner and the compression specification alone, the physical procedure
returns the true rational-side decision and stays within its combined price-query budget. -/
theorem subspaceDecisionRun_spec (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (hD : LinearIndependent ℚ D.row) (hE : LinearIndependent ℚ E.row) (hDE : D * Eᵀ = 0)
    (hsize : r+s=n) (anchor : Fin n) (F : ℕ) (hF : 1 ≤ F)
    (request : MinorRequest (NonzeroPairMinor D E)) (hreq : SubspaceRequestCorrect D E request F)
    (maxQueries : ℕ) (learner : PriceGame.Tree n) (hClock : learner.height ≤ maxQueries)
    (sound : ∀ h : Hidden n (2*F) anchor, PriceGame.Tree.Correct h learner) :
    ∃ b : Bool, (subspaceDecisionRun D E request maxQueries learner).value = some b ∧
      (b = true ↔ ∃ x ∈ span ℚ (Set.range D.row), 0 ≤ x ∧ 0 < x anchor) ∧
      (subspaceDecisionRun D E request maxQueries learner).log.length ≤ (minorRestartBudget n + 1) * (maxQueries + 1) := by
  obtain ⟨l, herr, test, extend⟩ := hreq
  obtain ⟨flag, hflag, hanchor⟩ := exists_winning_circuit_side D E hD hE hDE hsize anchor
  let C (f : NonzeroPairMinor D E → ℚ) := if flag then minorCircuitFamily D (prefixAssignment D E f)
    else minorCircuitFamily E (dualPrefixAssignment D E f)
  have cap (J : Finset (NonzeroPairMinor D E)) (hJ : IsDissociated l J) : J.card ≤ minorRestartBudget n :=
    (generatorCap_of_minor_proxy D E anchor.pos hsize l herr J hJ).trans (ceil_minorCap_le_budget n)
  have hbound (f) (hf : AdmissibleMinorAssignment D E F f) (i) (hi : 0 < circuitEnvelope (C f) i) :
      circuitCost (C f) i ∈ Set.Icc 0 ((2*F : ℕ) : ℝ) := by
    have hb := prefixAssignment_bounds D E f (Nat.cast_nonneg F) hf.1
    by_cases hside : flag = true
    · rw [show C f = minorCircuitFamily D (prefixAssignment D E f) from ite_eq_left hside] at hi ⊢
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        minorCircuitFamily_costBound D _ (fun k => (hb k).1) i hi
    · rw [show C f = minorCircuitFamily E (dualPrefixAssignment D E f) from ite_eq_right hside] at hi ⊢
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        minorCircuitFamily_costBound E _ (fun k => (hb k).2) i hi
  have hv (f) (hf : AdmissibleMinorAssignment D E F f) (q : PriceGame.Query n) :
      ValidNearLabel (C f) flag q ((geometricLabel D E q.prices q.index).eval f) := by
    have hg := geometricLabel_correct_assignment D E hD hE hsize hDE f hf.2 q
    dsimp only [C]
    cases flag
    · exact hg.2
    · exact hg.1
  have hout := generatorService_recovers (by omega : 1 ≤ 2*F) anchor learner maxQueries hClock sound request
    (fun q : PriceGame.Query n => geometricLabel D E q.prices q.index) l test (minorRestartBudget n) cap
    (AdmissibleMinorAssignment D E F) extend flag C (fun f _ => hanchor (prefixAssignment D E f) (dualPrefixAssignment D E f)) hbound hv
  exact ⟨flag, hout.1, hflag, hout.2⟩

theorem subspaceDecision_correct (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (hD : LinearIndependent ℚ D.row) (hE : LinearIndependent ℚ E.row) (hDE : D * Eᵀ = 0)
    (hsize : r+s=n) (anchor : Fin n) (F : ℕ) (hF : 1 ≤ F)
    (request : MinorRequest (NonzeroPairMinor D E)) (hreq : SubspaceRequestCorrect D E request F)
    (maxQueries : ℕ) (learner : PriceGame.Tree n) (hClock : learner.height ≤ maxQueries)
    (sound : ∀ h : Hidden n (2*F) anchor, PriceGame.Tree.Correct h learner) :
    subspaceDecision D E request maxQueries learner = true ↔ ∃ x ∈ span ℚ (Set.range D.row), 0 ≤ x ∧ 0 < x anchor := by
  obtain ⟨b, hrun, hwin, _⟩ := subspaceDecisionRun_spec D E hD hE hDE hsize anchor F hF request hreq maxQueries learner hClock sound
  simpa only [subspaceDecision, hrun, Option.getD_some] using hwin

/-- Total physical minor requests across all restarts, including each one that interrupted
its price query. This multiplies the actual geometric bound `r*n` by the outer query budget. -/
theorem subspaceDecisionRun_minorCalls (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (hD : LinearIndependent ℚ D.row) (hE : LinearIndependent ℚ E.row) (hDE : D * Eᵀ = 0)
    (hsize : r+s=n) (anchor : Fin n) (F : ℕ) (hF : 1 ≤ F)
    (request : MinorRequest (NonzeroPairMinor D E)) (hreq : SubspaceRequestCorrect D E request F)
    (maxQueries : ℕ) (learner : PriceGame.Tree n) (hClock : learner.height ≤ maxQueries)
    (sound : ∀ h : Hidden n (2*F) anchor, PriceGame.Tree.Correct h learner) :
    priceLogMinorCalls request (fun q : Query n => geometricLabel D E q.prices q.index) ∅
      (subspaceDecisionRun D E request maxQueries learner).log ≤
        (minorRestartBudget n + 1) * (maxQueries + 1) * (r*n) := by
  obtain ⟨_, _, _, hlen⟩ := subspaceDecisionRun_spec D E hD hE hDE hsize anchor F hF request hreq maxQueries learner hClock sound
  exact (priceLogMinorCalls_le request _ (fun q : PriceGame.Query n => geometricLabel_bounded D E q.prices q.index)
    _ _).trans (Nat.mul_le_mul_right _ hlen)

end Geometry
end LinearProgramming
end Optimization
end OAI
