import OAI.Computability.BorderVNP.PackedBandLookup

/-! # Public inverse-permutation reads for hook destinations

The pool of direction d in bin a belongs to the seed at the inverse-permuted address. One
fixed table per direction suffices, independently of the actual bins of the live cables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PoolCircuit

open PackedHistogram VPVNP.VerifierNetwork ParseBatchSort Shortening

/-- Obtain all inverse seed addresses in a single parallel batch of sort-and-scan reads. -/
theorem inverse_seed_frames {A : Type} {U σ : Type*} [Fintype A] [Fintype U] [Fintype σ]
    (D k w : ℕ) (p : PublicPopulation.Pins U σ k w) (code : A ↪ Fin (2^k))
    (name : A → Fin (2^w)) (perm : Fin D → Equiv.Perm A) :
    let n := Fintype.card A + Fintype.card U
    ∃ f : Frame σ (U × Fin D × Fin w),
      f.size ≤ 1 + D * (2*(n+1)*PublicPopulation.laneCost (Nat.clog 2 n) k w) ∧
      ∀ (x : σ → Bool) u a, value (x ∘ p.key u) = (code a).val →
        ∀ d, value (fun j => f.eval x (u,d,j)) = (name ((perm d).symm a)).val := by
  intro n
  let row (d : Fin D) := PackedLookup.lookup (layout A U) code
    (fun a => fixed (name ((perm d).symm a))) (fun u j => .input (p.key u j))
  obtain ⟨g,hg,eg⟩ := Crossing.exists_parallelFrames row
  refine ⟨g.select (fun z => ⟨z.2.1,z.1,z.2.2⟩),?_,?_⟩
  · have pad : 2^(Nat.clog 2 n) ≤ 2*(n+1) := by
      by_cases hz : n = 0
      · simp [hz]
      · exact (layout_size A U (Nat.pos_of_ne_zero hz)).le.trans (by dsimp [n]; omega)
    have hr (d : Fin D) : (row d).size ≤ 2*(n+1)*PublicPopulation.laneCost (Nat.clog 2 n) k w := by
      apply (queries_size _ _ _ _ 3 (by decide)
        (fun _ _ => by change 1 ≤ 3; decide)
        (fun _ _ => by change 1 ≤ 3; decide)
        (fun _ _ => by change 1 ≤ 3; decide)).trans
      exact Nat.mul_le_mul_right _ pad
    rw [Frame.select_size]
    exact hg.trans (Nat.add_le_add_left (by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun d _ => hr d)) 1)
  · intro x u a hu d
    simp only [Frame.select_eval,eg]
    exact (PackedLookup.lookup_value (layout A U) code (fun a => fixed (name ((perm d).symm a)))
      (fun u j => .input (p.key u j)) x u a hu).trans (fixed_value _ _)

end Packing.PoolCircuit

end BorderVNP
end Computability
end OAI
