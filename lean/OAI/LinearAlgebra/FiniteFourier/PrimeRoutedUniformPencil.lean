import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedUniform
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedAssembly

/-! # A uniform prime-template program for the entire routed pencil -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open scoped Classical

variable {K : Type*} [CommSemiring K] {ℓ : ℕ} {F : ℕ → ℕ} {ζ : K}
variable {X : ℕ → Type} [∀ f, Fintype (X f)]
variable {L W A C U J : Type} [Fintype L] [Fintype W] [Fintype A]
  [Fintype C] [Fintype U] [Fintype J]

/-- Summing the rectangle programs incurs linear local work, with a uniform
constant across digit lengths. Calls inside free rectangles are shared across
queries, while charged rectangles spend one batch of calls per query. -/
theorem routedPencil_uniform
    (cs ct : C → Set L) (fs ft : U → Set L) (cw : C → K) (fw : U → K)
    (hid : ∀ v w : L,
      (∑ r, if v ∈ cs r ∧ w ∈ ct r then cw r else 0) +
      (∑ r, if v ∈ fs r ∧ w ∈ ft r then fw r else 0) = if v = w then 1 else 0)
    (B₀ : Matrix W W K) (B : A → J → Matrix W W K)
    (H : (f : ℕ) → A → J → L → L → Matrix (X f) (X f) K)
    (Q : (f : ℕ) → A → J → Matrix (X f) (X f) K)
    (hdiag : ∀ f a j v, H f a j v v = Q f a j) (k : ℕ)
    (charged : ∀ a r j, LinearRowTemplate ℓ F ζ X (fun f =>
      routedRectangleMatrix (cs r) (ct r) (cw r) (routedPencilTerm (B a j) (H f a j)))
      (Fintype.card W * k))
    (free : ∀ a r, LinearRowTemplate ℓ F ζ X (fun f =>
      routedRectangleMatrix (fs r) (ft r) (fw r) (∑ j, routedPencilTerm (B a j) (H f a j)))
      (Fintype.card W * (Fintype.card (ft r) + Fintype.card (fs r)) * k)) :
    LinearRowTemplate ℓ F ζ X (fun f => routedPencilMatrix (L := L) B₀ B (Q f))
      (Fintype.card A * (Fintype.card C * Fintype.card J * Fintype.card W * k +
        Fintype.card W * (∑ r, (Fintype.card (ft r) + Fintype.card (fs r))) * k)) := by
  have cst : LinearRowTemplate ℓ F ζ X
      (fun f => routedConstantMatrix (L := L) (X := X f) B₀) 0 := by
    exact ⟨_, fun f _ => ⟨_, le_rfl, 0, le_rfl, routedConstant_template B₀⟩⟩
  have cp (a : A) := LinearRowTemplate.sum_finset Finset.univ (fun r _ =>
    LinearRowTemplate.sum_finset Finset.univ (fun j _ => charged a r j))
  have fp (a : A) := LinearRowTemplate.sum_finset Finset.univ (fun r _ => free a r)
  have total := cst.add (LinearRowTemplate.sum_finset Finset.univ (fun a _ => (cp a).add (fp a)))
  have p := total.congr fun f => routedPencil_assembly cs ct fs ft cw fw hid B₀ B (H f) (Q f) (hdiag f)
  simpa [← Finset.sum_mul, ← Finset.mul_sum, Nat.mul_assoc] using p

end

end

end FiniteFourier
end LinearAlgebra
end OAI
