import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridProduct
import OAI.LinearAlgebra.FiniteFourier.CircuitParallel

/-! # Independent coordinate circuits on all prime-axis sectors

The active axes of a sector can be read from its tuple of optional
coordinates. Relabeling this tuple at the input and output lets each
sector use its own circuit, including when the precision changes.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid
open scoped Classical

variable {σ : Type*} [Fintype σ] {K : σ → Type*}

private noncomputable def sectorWires (T : Type*) :
    (Σ S : Finset σ, (∀ i : S, K i.val) × T) ≃ (∀ i, Option (K i)) × T :=
  (Equiv.sigmaProdDistrib _ T).symm.trans (sectorEquiv.prodCongr (Equiv.refl T))

private theorem sectorWires_mk {T : Type*} (S : Finset σ) (k : ∀ i : S, K i.val) (t : T) :
    sectorWires T ⟨S,k,t⟩ = (sectorIndex S k,t) := rfl

/-- Run one circuit per sector with no gates charged for the input and output
permutations. The coordinate attached to each sector row can change type. -/
theorem circuit_sectors {R T V : Type*} [Semiring R] {c : Finset σ → ℕ}
    (p : ∀ S : Finset σ, Circuit R ((∀ i : S, K i.val) × T) ((∀ i : S, K i.val) × V) (c S)) :
    ∃ n ≤ ∑ S, c S, ∃ q : Circuit R ((∀ i, Option (K i)) × T) ((∀ i, Option (K i)) × V) n,
      ∀ (S : Finset σ) (k : ∀ i : S, K i.val) (v : V) x,
        q.eval x (sectorIndex S k,v) = (p S).eval (fun z => x (sectorIndex S z.1,z.2)) (k,v) := by
  classical
  obtain ⟨n,hn,q,hq⟩ := circuit_family p
  refine ⟨n, hn, q.rewire (fun i => (1, sectorWires T i)) (fun o => (1, (sectorWires V).symm o)), ?_⟩
  intro S k v x
  rw [Circuit.eval_rewire, ← sectorWires_mk, Equiv.symm_apply_apply]
  simp only [one_mul, hq]
  rfl

/-- Summing sector sizes counts each optional coordinate tuple once. -/
theorem sum_card_sectors [∀ i, Fintype (K i)] :
    ∑ S : Finset σ, Fintype.card (∀ i : S, K i.val) = Fintype.card (∀ i, Option (K i)) := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr sectorEquiv

/-- On an odd prime axis the scalar row plus the quadratic-binomial rows
recover exactly the prime number of monomial coordinates. -/
theorem card_atTwoGrid (p : σ → ℕ) (hp : ∀ i, p i % 4 = 3) :
    Fintype.card (∀ i, Option (Fin 2 × Fin ((p i-1)/2))) = ∏ i, p i := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
  have := hp i
  omega

/-- The total number of rows across all active subsets is the grid volume. -/
theorem sum_card_atTwoSectors (p : σ → ℕ) (hp : ∀ i, p i % 4 = 3) :
    ∑ S : Finset σ, Fintype.card (∀ i : S, Fin 2 × Fin ((p i.val-1)/2)) = ∏ i, p i :=
  (sum_card_sectors (K := fun i => Fin 2 × Fin ((p i-1)/2))).trans (card_atTwoGrid p hp)

end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI
