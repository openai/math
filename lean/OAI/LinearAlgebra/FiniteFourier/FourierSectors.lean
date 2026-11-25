import OAI.LinearAlgebra.FiniteFourier.PrimeDigits
import OAI.LinearAlgebra.FiniteFourier.CircuitParallel
import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization

/-! # Fourier sectors in a heterogeneous tensor stage

Each factor acts on a disjoint union of active tuples and inactive singletons.
Choosing one part in each factor gives a sector of the full tensor product.
The algorithm runs one prime Fourier tensor circuit on each sector.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

variable {R : Type*} [CommRing R]

/-- One synchronized Fourier stage on a local array. Each block has either
one active digit or zero digits, in which case it is a fixed coordinate. -/
structure PrimeFourierSectors (p : ℕ) (ζ : R) {I : Type} (A : Matrix I I R) where
  B : Type
  [fb : Fintype B]
  [eb : DecidableEq B]
  digits : B → ℕ
  e : (Σ b, Fin (digits b) → Fin p) ≃ I
  block : A.submatrix e e = Matrix.blockDiagonal' (fun b => primeTransform p (digits b) ζ)
  one_digit : ∀ b, digits b ≤ 1

attribute [instance] PrimeFourierSectors.fb PrimeFourierSectors.eb

variable {p : ℕ} {ζ : R} {ι : Type} [Fintype ι] {I : ι → Type}
    {A : ∀ i, Matrix (I i) (I i) R} (D : ∀ i, PrimeFourierSectors p ζ (A i))

private abbrev Labels := ∀ i, (D i).B

private abbrev Digits (b : Labels D) := Σ i, Fin ((D i).digits (b i))

/-- A point of the full array chooses local sector labels, then one value
for each active digit in their disjoint union. -/
private def sectorEquiv : (Σ b : Labels D, Digits D b → Fin p) ≃ (∀ i, I i) :=
  let assemble : (Σ b : Labels D, ∀ i, Fin ((D i).digits (b i)) → Fin p) ≃
      (∀ i, Σ b, Fin ((D i).digits b) → Fin p) :=
    ⟨fun ⟨b,x⟩ i => ⟨b i, x i⟩, fun y => ⟨fun i => (y i).1, fun i => (y i).2⟩,
      fun _ => rfl, fun _ => rfl⟩
  ((Equiv.sigmaCongrRight fun b : Labels D =>
    Equiv.piCurry (fun i (_ : Fin ((D i).digits (b i))) => Fin p)).trans assemble).trans
      (Equiv.piCongrRight fun i => (D i).e)

private def digitTransform (S : Type) [Fintype S] (p : ℕ) (ζ : R) :
    Matrix (S → Fin p) (S → Fin p) R :=
  fun x y => ∏ i, ζ ^ ((x i).val * (y i).val)

private theorem digitTransform_cost (S : Type) [Fintype S] (p : ℕ) (ζ : R) :
    RealizableAtMost (digitTransform S p ζ) (complexity (primeTransform p (Fintype.card S) ζ)) := by
  let g := Fintype.equivFin S
  let f := g.symm.arrowCongr (Equiv.refl (Fin p))
  have h := (realizableAtMost_complexity (primeTransform p (Fintype.card S) ζ)).reindex f f
  convert h using 1
  ext x y
  exact Fintype.prod_equiv g _ _ (fun i => by simp [f])

private theorem sectorEquiv_block [DecidableEq ι] :
    (gridTensor A).submatrix (sectorEquiv D) (sectorEquiv D) =
      Matrix.blockDiagonal' (fun b : Labels D => digitTransform (Digits D b) p ζ) := by
  ext ⟨b,x⟩ ⟨c,y⟩
  by_cases hbc : b = c
  · subst c
    rw [Matrix.blockDiagonal'_apply_eq]
    change (∏ i, A i ((D i).e ⟨b i, fun t => x ⟨i,t⟩⟩)
      ((D i).e ⟨b i, fun t => y ⟨i,t⟩⟩)) = ∏ i, ζ ^ ((x i).val * (y i).val)
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    exact (congrFun₂ (D i).block ⟨b i, fun t => x ⟨i,t⟩⟩ ⟨b i, fun t => y ⟨i,t⟩⟩).trans
      (Matrix.blockDiagonal'_apply_eq ..)
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hbc]
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := not_forall.mp fun he => hbc (funext he)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact (congrFun₂ (D i).block ⟨b i, fun t => x ⟨i,t⟩⟩ ⟨c i, fun t => y ⟨i,t⟩⟩).trans
      (Matrix.blockDiagonal'_apply_ne _ _ _ hi)

include D in
/-- Summing the Fourier circuits on the heterogeneous sectors does not lose
a factor equal to the number of digit positions or the number of sectors. -/
theorem primeFourierSectors_grid_bound [DecidableEq ι] [∀ i, Fintype (I i)] {β C : ℝ}
    (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hcost : ∀ k ≤ Fintype.card ι, (complexity (primeTransform p k ζ) : ℝ) ≤
      C * (p : ℝ)^k * (1 + (k : ℝ))^β) :
    (complexity (gridTensor A) : ℝ) ≤
      C * (Fintype.card (∀ i, I i) : ℝ) * (1 + (Fintype.card ι : ℝ))^β := by
  classical
  let k (b : Labels D) := Fintype.card (Digits D b)
  have hk b : k b ≤ Fintype.card ι := by
    simpa [k, Digits, Fintype.card_sigma] using
      (Finset.sum_le_sum (s := Finset.univ) fun i _ => (D i).one_digit (b i))
  have hvol : ∑ b : Labels D, (p : ℝ)^(k b) = Fintype.card (∀ i, I i) := by
    exact_mod_cast (by simpa [Fintype.card_sigma, k] using Fintype.card_congr (sectorEquiv D) :
      ∑ b : Labels D, p^(k b) = Fintype.card (∀ i, I i))
  have hblock := RealizableAtMost.blockDiagonal' (fun b : Labels D =>
    digitTransform_cost (Digits D b) p ζ)
  rw [← sectorEquiv_block D] at hblock
  have hsum : complexity (gridTensor A) ≤ ∑ b : Labels D, complexity (primeTransform p (k b) ζ) := by
    simpa [Matrix.submatrix_submatrix] using
      (complexity_le_iff _ _).mpr (hblock.submatrix (sectorEquiv D).symm (sectorEquiv D).symm.toEmbedding)
  calc
    _ ≤ ∑ b : Labels D, (complexity (primeTransform p (k b) ζ) : ℝ) := by exact_mod_cast hsum
    _ ≤ ∑ b : Labels D, C * (p : ℝ)^(k b) * (1 + (Fintype.card ι : ℝ))^β := by
      apply Finset.sum_le_sum
      intro b _
      refine (hcost _ (hk b)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_left (hk b) 1) hβ
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, hvol]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
