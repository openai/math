import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointSplit
import OAI.LinearAlgebra.FiniteFourier.PrimeCommonKernel

/-! # Separation of the free-rectangle query kernel

In charts adapted to the input and output summation spaces, the cross phase
splits into two Fourier phases and a phase of the coset representatives.
The input and output chirps on the distinguished digit depend only on those
representatives. They can therefore be included in the intervening monomial.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

variable {ℓ : ℕ} {V C : Type*} [Fintype C] [AddCommGroup V] [Module (ZMod ℓ) V]

/-- Paired first and second halves of a single row at all columns. -/
def endpointSelfPair (B : LinearMap.BilinForm (ZMod ℓ) V) (x : (C → V) × (C → V)) : ZMod ℓ :=
  ∑ c, B (x.1 c) (x.2 c)

/-- The two cross terms of the ordinary quadratic kernel. -/
def endpointCrossPair (B : LinearMap.BilinForm (ZMod ℓ) V) (x z : (C → V) × (C → V)) : ZMod ℓ :=
  ∑ c, (B (x.1 c) (z.2 c) + B (z.1 c) (x.2 c))

theorem endpointPair_quadratic (B : LinearMap.BilinForm (ZMod ℓ) V)
    (x z : (C → V) × (C → V)) :
    (∑ c, B (x.1 c - z.1 c) (z.2 c - x.2 c)) =
      endpointCrossPair B x z - endpointSelfPair B x - endpointSelfPair B z := by
  unfold endpointSelfPair endpointCrossPair
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simp only [map_sub, LinearMap.sub_apply]
  ring

variable {K H P S T U : Type*} [CommRing K] [NeZero ℓ] [Invertible (ℓ : K)]
variable [Fintype H] [Fintype P] [Fintype S] [Fintype T]
variable {ζ : K}

private theorem endpoint_weighted_chain {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (A : Matrix O O K) (M : Matrix O I K) (E : Matrix I I K) (u : I → K) (v : O → K)
    (o : O) (i : I) :
    ((Matrix.diagonal v * A) * (M * (E * Matrix.diagonal u))) o i =
      v o * ((A * (M * E)) o i * u i) := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc M E, ← Matrix.mul_assoc A (M * E),
    Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Given the two residual-coordinate permutations, apply the Fourier kernels
of the two summation spaces only at the endpoints. The bridge is a zero-gate
scaled permutation. All assumptions on the phases are identities in the digit
field, so scalar specialization of the resulting formula is exact. -/
theorem primeCommonKernel_free_factor (hζ : IsPrimitiveRoot ζ ℓ)
    (B : LinearMap.BilinForm (ZMod ℓ) V) (a : (ZMod ℓ)ˣ) (D : ℕ)
    (x : H × S → PrimeCommonAddress C V U) (z : P × T → PrimeCommonAddress C V U)
    (s : S ≃ P × U) (t : T ≃ H × U)
    (f : H → H → ZMod ℓ) (g : P → P → ZMod ℓ) (r : S → T → ZMod ℓ)
    (auxX : H × S → ZMod ℓ) (auxZ : P × T → ZMod ℓ) (dX : S → ZMod ℓ) (dZ : T → ZMod ℓ)
    (hs : ∀ i, (x i).2 = (s i.2).2) (ht : ∀ o, (z o).2 = (t o.2).2)
    (hx : ∀ i, endpointSelfPair B (x i).1 = auxX i + dX i.2)
    (hz : ∀ o, endpointSelfPair B (z o).1 = auxZ o + dZ o.2)
    (hc : ∀ i o, endpointCrossPair B (x i).1 (z o).1 =
      f (t o.2).1 i.1 + g o.1 (s i.2).1 + r i.2 o.2) :
    let e := (↑(a⁻¹) : ZMod ℓ)
    let F : Matrix H H K := fun freq h => digitPhase hζ (e * f freq h)
    let G : Matrix P P K := fun p μ => digitPhase hζ (e * g p μ)
    let w := fun (o : P × T) =>
      let u := s.symm (o.1, (t o.2).2)
      (⅟(ℓ : K)) ^ (Fintype.card C * D) * digitPhase hζ (e * (r u o.2 - dX u - dZ o.2))
    let source := endpointPartial F S * Matrix.diagonal (fun i => digitPhase hζ (-e * auxX i))
    let dest := Matrix.diagonal (fun o => digitPhase hζ (-e * auxZ o)) * endpointPartial G T
    (primeCommonKernel hζ B a D).submatrix z x = dest * (endpointBridge s t w * source) := by
  classical
  intro e F G w source dest
  ext o i
  change (primeCommonKernel hζ B a D).submatrix z x o i =
    ((Matrix.diagonal (fun o => digitPhase hζ (-e * auxZ o)) * endpointPartial G T) *
      (endpointBridge s t w * (endpointPartial F S *
        Matrix.diagonal (fun i => digitPhase hζ (-e * auxX i))))) o i
  refine Eq.trans ?_ (endpoint_weighted_chain (endpointPartial G T) (endpointBridge s t w) (endpointPartial F S)
    (fun i => digitPhase hζ (-e * auxX i)) (fun o => digitPhase hζ (-e * auxZ o)) o i).symm
  rw [endpointPartial_bridge_partial_apply]
  simp only [Matrix.submatrix_apply, primeCommonKernel, hs, ht]
  by_cases h : (s i.2).2 = (t o.2).2
  · have hsi : s.symm ((s i.2).1, (t o.2).2) = i.2 := by rw [← h]; simp
    simp only [ite_eq_left h, w, hsi, endpointPair_quadratic, hx, hz, hc]
    -- Combine the five phases while keeping the common normalization outside the character.
    let ψ := digitPhase hζ
    let b := (↑(a⁻¹) : ZMod ℓ)
    let n := (⅟(ℓ : K)) ^ (Fintype.card C * D)
    let u := f (t o.2).1 i.1
    let v := g o.1 (s i.2).1
    let k := r i.2 o.2
    change n * ψ (b * (u + v + k - (auxX i + dX i.2) - (auxZ o + dZ o.2))) =
      ψ (-b * auxZ o) * ((ψ (b * v) * (n * ψ (b * (k - dX i.2 - dZ o.2)) * ψ (b * u))) *
        ψ (-b * auxX i))
    rw [show b * (u + v + k - (auxX i + dX i.2) - (auxZ o + dZ o.2)) =
      (-b * auxZ o) + b * v + b * (k - dX i.2 - dZ o.2) + b * u + (-b * auxX i) by ring]
    simp only [AddChar.map_add_eq_mul]
    ring
  · simp [h]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
