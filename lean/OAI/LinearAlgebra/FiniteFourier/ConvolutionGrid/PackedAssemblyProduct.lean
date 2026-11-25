import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPackedAssemblyCircuit
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridProduct

/-! # Recovering the packed cyclic product from its split points

Every active sector certifies its own product. The inverse prime matrix
reassembles the sector products on the entire residue grid. This charges the
common input circuit twice and the return circuit once.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid

open Deformation Matrix Polynomial
open scoped Classical BigOperators

variable {R T G B : Type*} [CommRing R] [CommRing T] [Fintype G] [Add G] [DecidableEq G]

/-- The two packed circuits and the transformations they realize, with the
combined budget for multiplying two arbitrary input arrays. -/
def HasGridProductCircuits (φ : R →+* T) (η : T) (M : T[X]) (G : Type*)
    [Fintype G] [Add G] [DecidableEq G] (e r : ℕ) (H : B → ℕ) (cost : ℝ) : Prop :=
  ∃ (a d : ℕ)
    (q : Circuit R (G × ((Fin r × Fin e) × Fin 2)) (JetBlockInput (fun _ : B => e) H) a)
    (t : Circuit R (JetBlockInput (fun _ : B => e) H) (G × ((Fin r × Fin e) × Fin 2)) d)
    (f : (G → JetQuotient M r) → ∀ b, JetQuotient M (H b))
    (j : (∀ b, JetQuotient M (H b)) → G → JetQuotient M r),
    ((2*a+d : ℕ) : ℝ) ≤ cost ∧
    (∀ x b, jetBlockValue φ η (fun _ => M) (q.eval x) b = f (jetOperandArray φ η M x) b) ∧
    (∀ x, jetOperandArray φ η M (t.eval x) = j (jetBlockValue φ η (fun _ => M) x)) ∧
    (∀ x y, j (f x * f y) = cyclicProduct x y)

/-- Group the prime transforms' rows into sectors, apply each endpoint circuit
on its own rows, and reassemble the full cyclic product. -/
theorem exists_sectorProductCircuits {O S : Type*} [Fintype O] [Fintype S] {K : S → Type*}
    (E : (Σ s, K s) ≃ O) {φ : R →+* T} {η : T} {M : T[X]} {e r : ℕ} {H : S → ℕ}
    {C : Matrix O G (JetQuotient M r)} {D : Matrix G O (JetQuotient M r)}
    {a d : ℝ} {b c : S → ℝ}
    (hC : JetMatrixCircuit φ η M e r C a) (hD : JetMatrixCircuit φ η M e r D d)
    {f : ∀ s, (K s → JetQuotient M r) → (K s → JetQuotient M (H s))}
    {g : ∀ s, (K s → JetQuotient M (H s)) → (K s → JetQuotient M r)}
    (hf : ∀ s, JetStage φ η M e r (H s) (f s) (b s))
    (hg : ∀ s, JetStage φ η M e (H s) r (g s) (c s))
    (hrec : ∀ (x y : G → JetQuotient M r) (z : O → JetQuotient M r),
      (∀ s, (fun k => z (E ⟨s,k⟩)) =
        g s (f s (fun k => (C *ᵥ x) (E ⟨s,k⟩)) * f s (fun k => (C *ᵥ y) (E ⟨s,k⟩)))) →
      D *ᵥ z = cyclicProduct x y) :
    HasGridProductCircuits φ η M G e r (fun k : Σ s, K s => H k.1)
      (2*a+d+∑ s, (2*b s+c s)) := by
  obtain ⟨qsize, hqsize, q, hq⟩ := exists_sectorForwardCircuit E hC hf
  obtain ⟨tsize, htsize, t, ht⟩ := exists_sectorBackwardCircuit E hD hg
  let forward (x : G → JetQuotient M r) (k : Σ s, K s) :=
    f k.1 (fun j => (C *ᵥ x) (E ⟨k.1,j⟩)) k.2
  let backward (y : ∀ k : Σ s, K s, JetQuotient M (H k.1)) :=
    D *ᵥ fun o => g (E.symm o).1 (fun j => y ⟨(E.symm o).1,j⟩) (E.symm o).2
  refine ⟨qsize, tsize, q, t, forward, backward, ?_, fun x k => hq x k.1 k.2, ht, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    push_cast
    linarith
  · intro x y
    apply hrec
    intro s
    funext k
    exact congrArg (fun i : Σ s, K s => g i.1 (fun j =>
      forward x ⟨i.1,j⟩ * forward y ⟨i.1,j⟩) i.2) (E.symm_apply_apply ⟨s,k⟩)

end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI
