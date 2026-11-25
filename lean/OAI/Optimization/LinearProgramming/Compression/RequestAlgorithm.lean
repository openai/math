import OAI.Optimization.LinearProgramming.Compression.RequestGrid
import OAI.Optimization.LinearProgramming.Lattice.LLL

/-! The two outcomes of the finite request test and its reduction to rational arithmetic. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- The square of the graph norm computed using only rational arithmetic. -/
def requestGraphSquare {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) : ℚ :=
  ∑ i, (z i : ℚ)^2 + (∑ i, (z i : ℚ) * w i)^2

theorem requestGraphSquare_eq {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) :
    (requestGraphSquare w z : ℝ) = ‖requestGraph w z‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp [requestGraphSquare, requestForm]

/-- Inspect the rational graph basis in a fixed index order. -/
def requestCandidate {d : ℕ} (w : Fin d → ℚ) (g : Fin d → Fin d → ℤ) (last : Fin d) :
    Option (Fin d) :=
  (List.finRange d).find? fun i => decide (g i last ≠ 0 ∧
    requestGraphSquare w (g i) ≤ (requestCutoff d : ℚ)^2)

theorem requestGraphSquare_le_iff {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) :
    requestGraphSquare w z ≤ (requestCutoff d : ℚ)^2 ↔
      ‖requestGraph w z‖ ≤ requestCutoff d := by
  have hcast : requestGraphSquare w z ≤ (requestCutoff d : ℚ)^2 ↔
      (requestGraphSquare w z : ℝ) ≤ (requestCutoff d : ℝ)^2 := by norm_cast
  rw [hcast, requestGraphSquare_eq, sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg _)]

theorem requestCandidate_some {d : ℕ} {w : Fin d → ℚ} {g : Fin d → Fin d → ℤ}
    {last i : Fin d} (h : requestCandidate w g last = some i) :
    g i last ≠ 0 ∧ ‖requestGraph w (g i)‖ ≤ requestCutoff d := by
  have hs := List.find?_some h
  simpa only [decide_eq_true_eq, requestGraphSquare_le_iff] using hs

theorem requestCandidate_none {d : ℕ} {w : Fin d → ℚ} {g : Fin d → Fin d → ℤ}
    {last : Fin d} (h : requestCandidate w g last = none) :
    ¬ ∃ i, g i last ≠ 0 ∧ ‖requestGraph w (g i)‖ ≤ requestCutoff d := by
  rintro ⟨i,hn,hs⟩
  have him := List.find?_eq_none.mp h i (List.mem_finRange i)
  exact him (by simpa only [decide_eq_true_eq, requestGraphSquare_le_iff] using And.intro hn hs)

theorem requestGraph_ne_zero {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) (last : Fin d)
    (hn : z last ≠ 0) : requestGraph w z ≠ 0 := by
  intro h
  have he := congrArg (fun x : EuclideanSpace ℝ (Fin (d+1)) => x last.castSucc) h
  simp at he
  exact hn he

/-- From a genuine integer spanning family of the graph lattice, linear independence
and the LLL reduction inequalities suffice for the restart certificate. -/
theorem requestCandidate_none_dissociated {n : ℕ} (v : Fin (n+1) → ℝ)
    (w : Fin (n+1) → ℚ) (g : Fin (n+1) → Fin (n+1) → ℤ)
    (hprev : IsDissociated v (Finset.univ.erase (Fin.last n)))
    (hsign : RequestSigns v (fun i => w i) (((n+1)+2)*(requestCutoff (n+1)+3)))
    (hind : LinearIndependent ℝ (fun i => requestGraph w (g i)))
    (hr : OAI.Optimization.LinearProgramming.Lattice.LLLReduced (fun i => requestGraph w (g i)))
    (hspan : ∀ z : Fin (n+1) → ℤ, ∃ a : Fin (n+1) → ℤ,
      requestGraph w z = ∑ i, (a i : ℝ) • requestGraph w (g i))
    (hempty : requestCandidate w g (Fin.last n) = none) :
    IsDissociated v Finset.univ := by
  apply dissociated_of_request_search_empty v w g (Fin.last n) hprev hsign _ (requestCandidate_none hempty)
  intro z hn
  obtain ⟨a, ha⟩ := hspan z
  exact OAI.Optimization.LinearProgramming.Lattice.lll_short_prefix hind hr a ha
    (requestGraph_ne_zero w z (Fin.last n) hn)

/-- Given a rounded proxy vector and a reduced graph basis, run the actual request:
`none` requests a restart, while `some` contains the rational affine coefficients. -/
def runMinorRequest {n : ℕ} (w : Fin (n+1) → ℚ) (g : Fin (n+1) → Fin (n+1) → ℤ)
    (oracle : (Fin (n+1) → ℤ) → ℤ → Bool) (q : ℕ) : Option ((Fin n → ℚ) × ℚ) :=
  (requestCandidate w g (Fin.last n)).map fun i =>
    (requestSlope (g i), ((requestGridRun oracle (g i) (Fin.last n) q (requestCutoff (n+1))).1 : ℚ) / q)

/-- Correctness of both branches of the finite request, with the graph lattice basis
requirements separated from the numerical affine-sign oracle. -/
theorem runMinorRequest_spec {n : ℕ} (v : Fin (n+1) → ℝ) (w : Fin (n+1) → ℚ)
    (g : Fin (n+1) → Fin (n+1) → ℤ) (oracle : (Fin (n+1) → ℤ) → ℤ → Bool)
    (ho : ∀ z c, oracle z c = true ↔ requestForm v z + c < 0) (q : ℕ) (hq : 0 < q)
    (hprev : IsDissociated v (Finset.univ.erase (Fin.last n)))
    (hsign : RequestSigns v (fun i => w i) (((n+1)+2)*(requestCutoff (n+1)+3)))
    (hind : LinearIndependent ℝ (fun i => requestGraph w (g i)))
    (hr : OAI.Optimization.LinearProgramming.Lattice.LLLReduced (fun i => requestGraph w (g i)))
    (hspan : ∀ z : Fin (n+1) → ℤ, ∃ a : Fin (n+1) → ℤ,
      requestGraph w z = ∑ i, (a i : ℝ) • requestGraph w (g i)) :
    match runMinorRequest w g oracle q with
    | none => IsDissociated v Finset.univ
    | some (slope, offset) =>
      |v (Fin.last n) - (∑ i, (slope i : ℝ) * v i.castSucc + offset)| < (1 : ℝ)/q := by
  unfold runMinorRequest
  cases h : requestCandidate w g (Fin.last n) with
  | none => exact requestCandidate_none_dissociated v w g hprev hsign hind hr hspan h
  | some i =>
    obtain ⟨hne, hshort⟩ := requestCandidate_some h
    apply request_grid_affine_approx v oracle ho (g i) hne q _ hq
    exact request_residual_le v (g i) (Fin.last n) hne (abs_requestForm_le_of_basis v w _ hsign hshort)

end Compression
end LinearProgramming
end Optimization
end OAI
