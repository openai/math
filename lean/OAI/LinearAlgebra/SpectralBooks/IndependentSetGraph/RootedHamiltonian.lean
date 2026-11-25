import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.TourOptions

/-! # Rooted lists and full-cycle successor permutations -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace IndependentSetGraph

open scoped Classical BigOperators
noncomputable section

abbrev HamiltonianPerm (m : ℕ) := {p : Equiv.Perm (Fin m) // p.IsCycleOn Set.univ}

/-- The directed Hamiltonian-cycle polynomial in its successor-permutation convention. -/
def hamiltonianCyclePolynomial (R : Type*) [CommSemiring R] (m : ℕ) :
    MvPolynomial (Fin m × Fin m) R :=
  ∑ p : HamiltonianPerm m, ∏ a : Fin m, MvPolynomial.X (a, p.val a)

variable {m : ℕ} [NeZero m]

private theorem rotate_pow_zero (t : Fin m) : (finRotate m ^ t.val) 0 = t := by
  rw [Equiv.Perm.coe_pow, ← finCycle_eq_finRotate_iterate]
  simp [finCycle]

private def successorPerm (hm : 2 ≤ m) (π : RootedTour m) : HamiltonianPerm m := by
  let p := π.val * finRotate m * π.val⁻¹
  refine ⟨p, ?_⟩
  have hr : (finRotate m).IsCycleOn Set.univ := by
    have hs := (isCycle_finRotate_of_le hm).isCycleOn
    convert hs using 1
    ext a
    change True ↔ finRotate m a ≠ a
    exact iff_of_true trivial (Equiv.Perm.mem_support.mp ((support_finRotate_of_le hm).symm ▸ Finset.mem_univ a))
  simpa [p] using hr.conj (g := π.val)

private theorem successorPerm_apply (hm : 2 ≤ m) (π : RootedTour m) (t : Fin m) :
    (successorPerm hm π).val (π.val t) = π.val (finRotate m t) := by
  change (π.val * finRotate m * π.val⁻¹) (π.val t) = _
  simp [Equiv.Perm.mul_apply]

private theorem successorPerm_injective (hm : 2 ≤ m) : Function.Injective (successorPerm hm) := by
  intro π ρ he
  apply Subtype.ext
  apply Equiv.ext
  intro t
  have hav (τ : RootedTour m) : ((successorPerm hm τ).val ^ t.val) 0 = τ.val t := by
    change ((τ.val * finRotate m * τ.val⁻¹) ^ t.val) 0 = _
    have hzero : τ.val⁻¹ 0 = 0 := τ.val.injective (by simp [τ.property])
    rw [conj_pow, Equiv.Perm.mul_apply, hzero, Equiv.Perm.mul_apply, rotate_pow_zero]
  rw [← hav π, he, hav]

private theorem successorPerm_surjective (hm : 2 ≤ m) : Function.Surjective (successorPerm hm) := by
  intro p
  let orbit (t : Fin m) := (p.val ^ t.val) 0
  have hf : p.val.IsCycleOn (Finset.univ : Finset (Fin m)) := by simpa using p.property
  have hsur : Function.Surjective orbit := by
    intro a
    obtain ⟨n, hn, ha⟩ := hf.exists_pow_eq (Finset.mem_univ 0) (Finset.mem_univ a)
    exact ⟨⟨n, by simpa using hn⟩, ha⟩
  let e := Equiv.ofBijective orbit ⟨Finite.injective_iff_surjective.mpr hsur, hsur⟩
  let π : RootedTour m := ⟨e, by change (p.val ^ (0 : Fin m).val) 0 = 0; simp⟩
  refine ⟨π, Subtype.ext (Equiv.ext fun a => ?_)⟩
  obtain ⟨t, rfl⟩ := π.val.surjective a
  rw [successorPerm_apply]
  change (p.val ^ (finRotate m t).val) 0 = p.val ((p.val ^ t.val) 0)
  rw [← Equiv.Perm.mul_apply, ← pow_succ']
  apply (hf.pow_apply_eq_pow_apply (Finset.mem_univ 0)).mpr
  simpa [finRotate_apply, Fin.val_add, Fin.val_one, Nat.add_mod_mod] using Nat.mod_modEq (t.val + 1) m

theorem rootedTour_sum_eq_cycles {R : Type*} [CommMonoid R] [AddCommMonoid R] (hm : 2 ≤ m)
    (w : Fin m → Fin m → R) :
    (∑ π : RootedTour m, ∏ t, w (π.val t) (π.val (finRotate m t))) =
      ∑ p : HamiltonianPerm m, ∏ i, w i (p.val i) := by
  let e := Equiv.ofBijective (successorPerm hm) ⟨successorPerm_injective hm, successorPerm_surjective hm⟩
  rw [← e.sum_comp (fun p => ∏ i, w i (p.val i))]
  apply Finset.sum_congr rfl
  intro π _
  rw [← Equiv.prod_comp π.val (fun i => w i ((e π).val i))]
  apply Finset.prod_congr rfl
  intro t _
  exact congrArg (w (π.val t)) (successorPerm_apply hm π t).symm

end
end IndependentSetGraph

end SpectralBooks
end LinearAlgebra
end OAI
