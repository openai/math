import OAI.LinearAlgebra.FiniteFourier.ConvolutionGather
import OAI.LinearAlgebra.FiniteFourier.CircuitReindex

/-! # Recovering open convolution from quadratic coordinates

The product in the mixed-radix monomial basis has one coefficient in the
quadratic algebra at each address. Gathering the first base-ring coordinates
recovers ordinary convolution, since the sum in the quadratic algebra belongs
to the image of the base ring.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra S A]
variable {n E r N : ℕ}

/-- A basis with elements `1` and `η` supplies the quadratic coordinate
uniqueness used by the gather circuit. -/
theorem quadraticEncoding_injective_of_basis [Algebra R S]
    (η : S) (basis : Module.Basis (Fin 2) R S) (h0 : basis 0 = 1) (h1 : basis 1 = η) :
    Function.Injective (fun t : Fin 2 → R => algebraMap R S (t 0) + η * algebraMap R S (t 1)) := by
  have h (t : Fin 2 → R) : basis.equivFun.symm t =
      algebraMap R S (t 0) + η * algebraMap R S (t 1) := by
    simp [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, h0, h1, Algebra.smul_def,
      mul_comm]
  intro a b hab
  apply basis.equivFun.symm.injective
  simpa only [h] using hab

/-- A quadratic encoding with unique coordinates permits the mixed-radix gather
to read only the constant coordinate of each entry. -/
theorem exists_quadraticGather_circuit (φ : R →+* S) (η : S)
    (hinj : Function.Injective (fun t : Fin 2 → R => φ (t 0) + η * φ (t 1)))
    (b : Module.Basis (Fin E × Fin r × Fin N) S A)
    (u v w : A) (hb : ∀ i, b i = u^i.1.val * v^i.2.1.val * w^i.2.2.val)
    (he : 0 < E) (hr : 0 < r) (hcap : 8*n ≤ E*r*N) :
    ∃ s ≤ E*r*N, ∃ p : Circuit R ((Fin E × Fin r × Fin N) × Fin 2) (Fin (2*n-1)) s,
      ∀ (x y : Fin n → R) (z : (Fin E × Fin r × Fin N) × Fin 2 → R),
      (∀ i, φ (z (i,0)) + η * φ (z (i,1)) =
        b.repr (packConvolutionInput b he hr hcap (φ ∘ x) *
          packConvolutionInput b he hr hcap (φ ∘ y)) i) →
      ∀ k, p.eval z k = openConv R n x y k := by
  classical
  obtain ⟨s, hs, q, hq⟩ := exists_convolutionGather_circuit R E r N n
  refine ⟨s, hs, q.rewire (fun i => (1,(i,0))) (fun k => (1,k)), ?_⟩
  intro x y z hz k
  let coords : Fin 2 → R := fun d =>
    ∑ i : Fin E × Fin r × Fin N, if packingAddress E r i = k.val then z (i,d) else 0
  let target : Fin 2 → R := fun d => if d = 0 then openConv R n x y k else 0
  have henc : φ (coords 0) + η * φ (coords 1) = φ (target 0) + η * φ (target 1) := by
    simp only [target, ite_true, one_ne_zero, ite_false, map_zero, mul_zero, add_zero,
      openConv_map]
    rw [← gather_packed_product b u v w hb he hr hcap (φ ∘ x) (φ ∘ y) k]
    simp only [coords, map_sum, apply_ite φ, map_zero, Finset.mul_sum,
      ← Finset.sum_add_distrib, gatherConvolutionOutput, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all [Module.Basis.coord_apply]
  have h := congrFun (hinj henc) 0
  simpa only [Circuit.eval_rewire, one_mul, hq, coords, target, ite_true] using h

end FiniteFourier
end LinearAlgebra
end OAI
