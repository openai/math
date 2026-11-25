import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Roots

/-! # Specialization of polynomial tensor coordinates

Each polynomial equation vanishing on a punctured affine polynomial curve
over an infinite field also vanishes at its specialization to zero.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {K ι : Type*} [Field K]

/-- Affine Zariski closure expressed by polynomial equations in the coordinates. -/
def affineZariskiClosure (S : Set (ι → K)) : Set (ι → K) :=
  {x | ∀ p : MvPolynomial ι K, (∀ y ∈ S, MvPolynomial.eval y p = 0) →
    MvPolynomial.eval x p = 0}

theorem subset_affineZariskiClosure (S : Set (ι → K)) : S ⊆ affineZariskiClosure S :=
  fun x hx _ hp ↦ hp x hx

@[simp] theorem affineZariskiClosure_idem (S : Set (ι → K)) :
    affineZariskiClosure (affineZariskiClosure S) = affineZariskiClosure S :=
  Set.Subset.antisymm (fun _ hx p hp ↦ hx p fun _ hy ↦ hy p hp)
    (subset_affineZariskiClosure _)

/-- Substitution into a polynomial equation transports vanishing along any
polynomial map of affine coordinate spaces. -/
theorem mapsTo_affineZariskiClosure_of_polynomial {κ : Type*}
    (f : κ → MvPolynomial ι K) {S : Set (ι → K)} {T : Set (κ → K)}
    (hf : Set.MapsTo (fun x j ↦ MvPolynomial.eval x (f j)) S T) :
    Set.MapsTo (fun x j ↦ MvPolynomial.eval x (f j)) (affineZariskiClosure S)
      (affineZariskiClosure T) := by
  intro x hx p hp
  change MvPolynomial.eval (MvPolynomial.eval x ∘ f) p = 0
  rw [MvPolynomial.eval_assoc]
  apply hx
  intro y hy
  rw [← MvPolynomial.eval_assoc]
  exact hp _ (hf hy)

/-- Fixed coordinate scalings preserving a set also preserve its closure. -/
theorem mapsTo_affineZariskiClosure_of_mul (s : ι → K) {S : Set (ι → K)}
    (hs : Set.MapsTo (fun x i ↦ s i * x i) S S) :
    Set.MapsTo (fun x i ↦ s i * x i) (affineZariskiClosure S) (affineZariskiClosure S) := by
  let f (i : ι) : MvPolynomial ι K := MvPolynomial.C (s i) * MvPolynomial.X i
  have heval (x : ι → K) (i : ι) : MvPolynomial.eval x (f i) = s i * x i := by simp [f]
  simpa only [heval] using mapsTo_affineZariskiClosure_of_polynomial f (S := S) (T := S)
    (by simpa only [heval] using hs)

/-- A polynomial curve contained in `S` away from zero specializes to a point
of its Zariski closure. This also applies to curves arising from local Laurent
weights when their total exponents on the support are nonnegative. -/
theorem polynomialCurve_zero_mem_affineZariskiClosure [Infinite K]
    (c : ι → Polynomial K) {S : Set (ι → K)}
    (hc : ∀ t : K, t ≠ 0 → (fun i ↦ (c i).eval t) ∈ S) :
    (fun i ↦ (c i).eval 0) ∈ affineZariskiClosure S := by
  intro p hp
  let f : Polynomial K := p.eval₂ Polynomial.C c
  have heval (t : K) : f.eval t = MvPolynomial.eval (fun i ↦ (c i).eval t) p := by
    have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id K := by ext; simp
    rw [show f = p.eval₂ Polynomial.C c from rfl, MvPolynomial.polynomial_eval_eval₂, hC,
      MvPolynomial.eval₂_id]
  have hf : f = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.finite_singleton (0 : K)).infinite_compl.mono
    intro t ht
    exact (heval t).trans (hp _ (hc t ht))
  rw [← heval, hf, Polynomial.eval_zero]

end SpectralBooks
end LinearAlgebra
end OAI
