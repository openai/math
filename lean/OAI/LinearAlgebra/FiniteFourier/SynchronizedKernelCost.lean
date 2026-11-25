import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization
import OAI.LinearAlgebra.FiniteFourier.CircuitParallel
import OAI.LinearAlgebra.FiniteFourier.SynchronizedKernel
import OAI.LinearAlgebra.FiniteFourier.PrimeFourierSectors.FourierSectorGenerators

/-! # Circuit cost of synchronized local kernel words

All local words run one Fourier stage at a time across the tensor factors.
The monomial slots collapse to free global scaled readouts.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R : Type*} [CommRing R]

private theorem kernelMonomial_free {J : Type} [DecidableEq J]
    (e : Equiv.Perm J) (c : J → R) : RealizableAtMost (kernelMonomial e c) 0 := by
  let q : Circuit R J J 0 := ⟨.nil, fun j => .scaled (c j) (.inl (e j))⟩
  refine ⟨0, le_rfl, q, ?_⟩
  ext i j
  rw [Circuit.matrix_apply]
  by_cases h : e i = j <;>
    simp [q, Circuit.eval, Readout.eval, kernelMonomial, h]

variable {ι : Type} [Fintype ι] {I : ι → Type} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

omit [∀ i, Fintype (I i)] in
private theorem kernelMonomial_grid_free (e : ∀ i, Equiv.Perm (I i)) (c : ∀ i, I i → R) :
    RealizableAtMost (gridTensor fun i => kernelMonomial (e i) (c i)) 0 := by
  classical
  let q := Equiv.piCongrRight e
  let a := fun x : ∀ i, I i => ∏ i, c i (x i)
  convert kernelMonomial_free q a using 1
  ext x y
  change (∏ i, if e i (x i) = y i then c i (x i) else 0) =
    if q x = y then a x else 0
  by_cases h : q x = y
  · subst y
    simp [q, a]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, e i (x i) ≠ y i := not_forall.mp fun h' => h (funext h')
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem KernelWord.grid_cost {p n S : ℕ} {ζ : R} {A : ∀ i, Matrix (I i) (I i) R}
    (h : ∀ i, KernelWord p ζ n (A i))
    (hF : ∀ (F : ∀ i, Matrix (I i) (I i) R), (∀ i, PrimeFourierSectors p ζ (F i)) →
      RealizableAtMost (gridTensor F) S) : RealizableAtMost (gridTensor A) (n * S) := by
  classical
  induction n generalizing A with
  | zero =>
    rw [show A = fun i => 1 from funext fun i => (h i : A i = 1), gridTensor_one, Nat.zero_mul]
    exact kernelMonomial_free (Equiv.refl _) (fun _ => 1)
  | succ n ih =>
    choose e c F P hF' hP hdec using h
    have hstage (i) : Nonempty (PrimeFourierSectors p ζ (F i)) := by
      rcases hF' i with hi | hi
      · rw [hi]
        exact ⟨PrimeFourierSectors.one p ζ _⟩
      · exact hi
    rw [show A = _ from funext hdec, gridTensor_mul, gridTensor_mul]
    simpa [Nat.succ_mul, Nat.add_comm] using
      (((hF F (fun i => (hstage i).some)).mul (kernelMonomial_grid_free e c)).mul (ih hP))

/-- Each synchronized slot costs at most the per-sector transform estimate
times the full tensor volume, independently of the matrices in the word. -/
theorem KernelWord.grid_bound [DecidableEq ι] {p n : ℕ} {ζ : R} {A : ∀ i, Matrix (I i) (I i) R}
    (h : ∀ i, KernelWord p ζ n (A i)) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hcost : ∀ k ≤ Fintype.card ι, (complexity (primeTransform p k ζ) : ℝ) ≤
      C * (p : ℝ)^k * (1 + (k : ℝ))^β) :
    (complexity (gridTensor A) : ℝ) ≤
      (n*C) * (Fintype.card (∀ i, I i) : ℝ) * (1 + (Fintype.card ι : ℝ))^β := by
  let S := C * (Fintype.card (∀ i, I i) : ℝ) * (1 + (Fintype.card ι : ℝ))^β
  have hs := KernelWord.grid_cost (S := ⌊S⌋₊) h (fun F D =>
    (complexity_le_iff _ _).mp (Nat.le_floor (primeFourierSectors_grid_bound D hβ hC hcost)))
  have hnat := (complexity_le_iff _ _).mpr hs
  have hS : 0 ≤ S := by dsimp [S]; positivity
  calc
    _ ≤ (n : ℝ) * (⌊S⌋₊ : ℝ) := by exact_mod_cast hnat
    _ ≤ (n : ℝ) * S := by gcongr; exact Nat.floor_le hS
    _ = _ := by dsimp [S]; ring

end FiniteFourier
end LinearAlgebra
end OAI
