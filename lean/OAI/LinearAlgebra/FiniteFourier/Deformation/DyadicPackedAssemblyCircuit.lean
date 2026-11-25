import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicDeformationStages
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssembly

/-! # Assembly of the prime grid and its deformation sectors

The prime transform has uniform jet height. Its rows split into sectors with
independent endpoint transforms, each of which can use a different jet height.
Grouping these rows and flattening the resulting split points only relabels
circuit wires.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial Matrix
open scoped BigOperators

variable {R T G O S : Type*} [CommRing R] [CommRing T] [Fintype S]
  {K : S → Type*} {φ : R →+* T} {η : T} {M : T[X]} {e r : ℕ}
  {H : S → ℕ} {a : ℝ} {b : S → ℝ}

/-- Run the common prime transform on a packed operand, then run the input
transform of each sector on its own short jets. -/
theorem exists_sectorForwardCircuit [Fintype G] (E : (Σ s, K s) ≃ O)
    {C : Matrix O G (JetQuotient M r)} (hC : JetMatrixCircuit φ η M e r C a)
    {f : ∀ s, (K s → JetQuotient M r) → (K s → JetQuotient M (H s))}
    (hf : ∀ s, JetStage φ η M e r (H s) (f s) (b s)) :
    ∃ t : ℕ, (t : ℝ) ≤ a + ∑ s, b s ∧
      ∃ p : Circuit R (G × ((Fin r × Fin e) × Fin 2))
        (JetBlockInput (fun _ : Σ s, K s => e) (fun j => H j.1)) t,
      ∀ x s (k : K s), jetBlockValue φ η (fun _ => M) (p.eval x) ⟨s,k⟩ =
        f s (fun j => (C *ᵥ jetOperandArray φ η M x) (E ⟨s,j⟩)) k := by
  obtain ⟨u, hu, prime, hprime⟩ := hC
  choose v hv sector hsector using hf
  obtain ⟨n, hn, family, hfamily⟩ := circuit_family sector
  let split := family.rewire
    (fun j => (1, (E ⟨j.1,j.2.1⟩,j.2.2)))
    (fun j : JetBlockInput (fun _ : Σ s, K s => e) (fun j => H j.1) =>
      (1, ⟨j.1.1,j.1.2,j.2⟩))
  obtain ⟨t, ht, p, hp⟩ := circuit_comp prime split
  refine ⟨t, ?_, p, fun x s k => ?_⟩
  · have hfam : (n : ℝ) ≤ ∑ s, (v s : ℝ) := by exact_mod_cast hn
    exact (show (t : ℝ) ≤ (u : ℝ) + n by exact_mod_cast ht).trans
      (add_le_add hu (hfam.trans (Finset.sum_le_sum fun s _ => hv s)))
  · let z (j : K s × ((Fin r × Fin e) × Fin 2)) := prime.eval x (E ⟨s,j.1⟩,j.2)
    have hs : (fun j => p.eval x ⟨⟨s,k⟩,j⟩) = fun j => (sector s).eval z (k,j) := by
      funext j
      simp [hp, split, Circuit.eval_rewire, hfamily, Function.comp_def, z]
    change jetOperandValue φ η M (fun j => p.eval x ⟨⟨s,k⟩,j⟩) = _
    rw [hs]
    change jetOperandArray φ η M ((sector s).eval z) k = _
    rw [hsector]
    have hz : jetOperandArray φ η M z = fun j => (C *ᵥ jetOperandArray φ η M x) (E ⟨s,j⟩) :=
      funext fun j => congrFun (hprime x) (E ⟨s,j⟩)
    rw [hz]

/-- Interpolate the split points independently in each sector and then apply
the common inverse prime transform to their short jets. -/
theorem exists_sectorBackwardCircuit [Fintype O] (E : (Σ s, K s) ≃ O)
    {D : Matrix G O (JetQuotient M r)} (hD : JetMatrixCircuit φ η M e r D a)
    {g : ∀ s, (K s → JetQuotient M (H s)) → (K s → JetQuotient M r)}
    (hg : ∀ s, JetStage φ η M e (H s) r (g s) (b s)) :
    ∃ t : ℕ, (t : ℝ) ≤ a + ∑ s, b s ∧
      ∃ p : Circuit R (JetBlockInput (fun _ : Σ s, K s => e) (fun j => H j.1))
        (G × ((Fin r × Fin e) × Fin 2)) t,
      ∀ x, jetOperandArray φ η M (p.eval x) =
        D *ᵥ (fun o => g (E.symm o).1
          (fun k => jetBlockValue φ η (fun _ => M) x ⟨(E.symm o).1,k⟩) (E.symm o).2) := by
  obtain ⟨u, hu, prime, hprime⟩ := hD
  choose v hv sector hsector using hg
  obtain ⟨n, hn, family, hfamily⟩ := circuit_family sector
  let join := family.rewire
    (fun j => (1, (⟨⟨j.1,j.2.1⟩,j.2.2⟩ : JetBlockInput
      (fun _ : Σ s, K s => e) (fun j => H j.1))))
    (fun j : O × ((Fin r × Fin e) × Fin 2) => (1, ⟨(E.symm j.1).1,(E.symm j.1).2,j.2⟩))
  obtain ⟨t, ht, p, hp⟩ := circuit_comp join prime
  refine ⟨t, ?_, p, fun x => ?_⟩
  · have hfam : (n : ℝ) ≤ ∑ s, (v s : ℝ) := by exact_mod_cast hn
    rw [add_comm]
    exact (show (t : ℝ) ≤ (n : ℝ) + u by exact_mod_cast ht).trans
      (add_le_add (hfam.trans (Finset.sum_le_sum fun s _ => hv s)) hu)
  · rw [hp, hprime]
    congr 1
    funext o
    let i := E.symm o
    let z (j : K i.1 × ((Fin (H i.1) × Fin e) × Fin 2)) := x ⟨⟨i.1,j.1⟩,j.2⟩
    have hs : (fun j => join.eval x (o,j)) = fun j => (sector i.1).eval z (i.2,j) := by
      funext j
      simp [join, Circuit.eval_rewire, hfamily, Function.comp_def, i, z]
    change jetOperandValue φ η M (fun j => join.eval x (o,j)) = _
    rw [hs]
    exact congrFun (hsector i.1 z) i.2

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
