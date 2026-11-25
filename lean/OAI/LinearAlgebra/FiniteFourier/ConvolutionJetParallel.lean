import OAI.LinearAlgebra.FiniteFourier.CircuitParallel

/-! # Independent linear circuits on the rows of a jet

The row index is a product when both coordinates in a quadratic power basis
are kept separately.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R I O : Type*} [Semiring R] {v : ℕ}

/-- Apply the same circuit on each row, with free input and output wiring. -/
theorem circuit_rows (T : Type*) [Fintype T] (p : Circuit R I O v) :
    ∃ s ≤ Fintype.card T * v, ∃ q : Circuit R (T × I) (T × O) s,
      ∀ (x : T × I → R) (t : T) (o : O),
        q.eval x (t, o) = p.eval (fun i => x (t, i)) o := by
  obtain ⟨s, hs, q, hq⟩ := circuit_family (fun _ : T => p)
  refine ⟨s, by simpa using hs,
    q.rewire (fun j => (1, (j.1, j.2))) (fun j => (1, ⟨j.1, j.2⟩)), ?_⟩
  intro x t o
  simp [Circuit.eval_rewire, hq, Function.comp_def]

/-- A row circuit on both base coordinates of a height-`h` jet takes at most
`2hv` gates. -/
theorem circuit_quadratic_rows (h : ℕ) (p : Circuit R I O v) :
    ∃ s ≤ 2*h*v, ∃ q : Circuit R ((Fin 2 × Fin h) × I) ((Fin 2 × Fin h) × O) s,
      ∀ (x : (Fin 2 × Fin h) × I → R) (b : Fin 2) (t : Fin h) (o : O),
        q.eval x ((b, t), o) = p.eval (fun i => x ((b, t), i)) o := by
  obtain ⟨s, hs, q, hq⟩ := circuit_rows (Fin 2 × Fin h) p
  exact ⟨s, by simpa using hs, q, fun x b t => hq x (b, t)⟩

end FiniteFourier
end LinearAlgebra
end OAI
