import OAI.Computability.NearSquareRoot.PhysicalWalshBaseField
import OAI.Computability.NearSquareRoot.PhysicalWalshRelease
import OAI.Computability.NearSquareRoot.KernelPassAxes
import OAI.Computability.NearSquareRoot.SynchronizedNorm
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Unitary target and roundoff of the physical two-bit base

The split permutation sends an ordinal to its two-bit digit and a spectator
ordinal. On these addresses the ideal pass is the normalized four-point
Walsh matrix tensored with the identity on the spectator. This yields one
Euclidean error bound over all physical records and a sufficient global
headroom condition at the base call.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshBase

open Matrix Kronecker KernelPass IntegerMultiplication SynchronizedPadding PhysicalWalsh.ChildLanes

noncomputable section

def digitKernel : Matrix (Fin 4) (Fin 4) ℂ := fun i j => pairEntry (bits i) (bits j)

private theorem digit_unitary : digitKernelᴴ * digitKernel = 1 := by
  let M := tensorMatrix (fun _ : Fin 2 => SynchronizedPair.walsh)
  let e : Fin 4 ≃ (Fin 2 → Fin 2) := (finFunctionFinEquiv (m:=2) (n:=2)).symm
  have he : digitKernel = M.submatrix e e := by
    ext i j
    exact pairEntry_complex _ _
  have hw : SynchronizedPair.walshᴴ = SynchronizedPair.walsh := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SynchronizedPair.walsh, conjTranspose_apply]
  have hh : Mᴴ*M = 1 := tensorMatrix_unitary _ (fun _ => by rw [hw, SynchronizedPair.walsh_sq])
  rw [he,conjTranspose_submatrix,submatrix_mul_equiv,hh,submatrix_one_equiv]

/-- The normalized two-bit layer in the original flat address coordinates. -/
def fieldKernel (P B : ℕ) : Matrix (Fin (P*4*B)) (Fin (P*4*B)) ℂ :=
  (digitKernel ⊗ₖ (1 : Matrix (Fin (P*B)) (Fin (P*B)) ℂ)).submatrix
    (laneEquiv P 4 B) (laneEquiv P 4 B)

theorem field_unitary (P B : ℕ) : (fieldKernel P B)ᴴ * fieldKernel P B = 1 := by
  rw [fieldKernel,conjTranspose_submatrix,submatrix_mul_equiv,conjTranspose_kronecker,
    conjTranspose_one,← mul_kronecker_mul,digit_unitary,one_mul,one_kronecker_one,submatrix_one_equiv]

/-- The actual encoded value at one physical ordinal. -/
def recordAt {P B w : ℕ} (x : Field P B w) (t : Fin (P*4*B)) : Dusk.Grain w :=
  x t.divNat.divNat t.divNat.modNat t.modNat

@[simp] theorem flat_records {P B w : ℕ} (x : Field P B w) :
    flat x = List.ofFn (fun t => Dusk.mark (recordAt x t)) := rfl

private theorem inverse_record {P B w : ℕ} (x : Field P B w) (j : Fin 4) (q : Fin (P*B)) :
    recordAt x ((laneEquiv P 4 B).symm (j,q)) = x q.divNat j q.modNat := by
  have d {m k : ℕ} (a : Fin m) (b : Fin k) : (finProdFinEquiv (a,b)).divNat = a :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (a,b))
  have r {m k : ℕ} (a : Fin m) (b : Fin k) : (finProdFinEquiv (a,b)).modNat = b :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (a,b))
  simp only [recordAt, laneEquiv, Equiv.coe_fn_symm_mk, d, r]

theorem fieldKernel_apply {P B : ℕ} (v : Fin (P*4*B) → ℂ) (t : Fin (P*4*B)) :
    (fieldKernel P B *ᵥ v) t = ∑ j, (pairEntry (bits ((laneEquiv P 4 B t).1)) (bits j) : ℂ) *
      v ((laneEquiv P 4 B).symm (j,(laneEquiv P 4 B t).2)) := by
  rw [fieldKernel,submatrix_mulVec_equiv]
  simp only [Function.comp_apply,mulVec,dotProduct,Fintype.sum_prod_type,kroneckerMap_apply,
    one_apply,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    digitKernel]

private theorem vector_apply {P B w : ℕ} (p : ℕ) (x : Field P B w) (j : Fin 4) (q : Fin (P*B)) :
    (fieldKernel P B *ᵥ (Grid.meaning p w ∘ recordAt x)) ((laneEquiv P 4 B).symm (j,q)) =
      ∑ a, (pairEntry (bits j) (bits a) : ℂ) * Grid.meaning p w (x q.divNat a q.modNat) := by
  rw [fieldKernel_apply]
  simp only [Equiv.apply_symm_apply,Function.comp_apply,inverse_record]

/-- One Euclidean norm test on the original row guarantees every two-bit
accumulation will fit when it is shifted back onto the tape. -/
theorem fitsField_of_norm {P B w : ℕ} (p : ℕ) (x : Field P B w) (M : ℝ)
    (hr : ‖(WithLp.toLp 2 (Grid.meaning p w ∘ recordAt x) : EuclideanSpace ℂ _)‖ ≤ M)
    (hw : M*2^p < 2^w) : ∀ g b, FitsGroup (fun j => x g j b) := by
  intro g b j
  let q : Fin (P*B) := finProdFinEquiv (g,b)
  have eqb : (q.divNat,q.modNat) = (g,b) := finProdFinEquiv.symm_apply_apply _
  let v : EuclideanSpace ℂ (Fin (P*4*B)) := WithLp.toLp 2 (Grid.meaning p w ∘ recordAt x)
  let T := matrixIsometry _ (field_unitary P B)
  have c := (PiLp.norm_apply_le (T v) ((laneEquiv P 4 B).symm (j,q))).trans ((T.norm_map v).le.trans hr)
  change ‖(fieldKernel P B *ᵥ (Grid.meaning p w ∘ recordAt x)) _‖ ≤ M at c
  have hqg : q.divNat = g := congrArg Prod.fst eqb
  have hqb : q.modNat = b := congrArg Prod.snd eqb
  rw [vector_apply,hqg,hqb] at c
  simp only [← coefficient_value] at c
  rw [← KernelPassMix.accum_meaning, norm_div, norm_pow, Complex.norm_ofNat, div_le_iff₀ (by positivity)] at c
  exact c.trans_lt hw

/-- Total physical row error. All `P*4*B` coordinates enter once. -/
theorem field_error {P B w : ℕ} (p : ℕ) (x : Field P B w) (fits : ∀ g b, FitsGroup (fun j => x g j b)) :
    ‖(WithLp.toLp 2 (Grid.meaning p w ∘ recordAt (applyField x)) : EuclideanSpace ℂ _) -
      matrixIsometry _ (field_unitary P B) (WithLp.toLp 2 (Grid.meaning p w ∘ recordAt x))‖ ≤
      Real.sqrt (Fintype.card (Fin (P*4*B))) * (2/(2:ℝ)^p) := by
  apply euclidean_norm_le_of_coordinates _ (by positivity)
  intro t
  obtain ⟨⟨j,q⟩,rfl⟩ := (laneEquiv P 4 B).symm.surjective t
  change ‖Grid.meaning p w (recordAt (applyField x) _) - (fieldKernel P B *ᵥ (Grid.meaning p w ∘ recordAt x)) _‖ ≤ _
  rw [inverse_record,vector_apply]
  exact entry_error p _ (fits _ _) _

/-- A bound on the input vector suffices to bound the error of the stored,
fixed-width output of the physical base command. -/
theorem storedField_error {P B w : ℕ} (p : ℕ) (x : Field P B w) (M : ℝ)
    (hr : ‖(WithLp.toLp 2 (Grid.meaning p w ∘ recordAt x) : EuclideanSpace ℂ _)‖ ≤ M)
    (hw : M*2^p < 2^w) :
    ‖(WithLp.toLp 2 (Grid.meaning p w ∘ recordAt (storedBase x)) : EuclideanSpace ℂ _) -
      matrixIsometry _ (field_unitary P B) (WithLp.toLp 2 (Grid.meaning p w ∘ recordAt x))‖ ≤
      Real.sqrt (P*4*B : ℕ) * (2/(2:ℝ)^p) := by
  have hs := fitsField_of_norm p x M hr hw
  rw [storedBase_eq x hs]
  simpa using field_error p x hs

/-- Release the unconditional split, mix and merge to a deterministic finite
tape machine with linear bounds on both transitions and visited cells. -/
theorem ordinalPhysical {I : Type} (P B w : I → ℕ) (r : (t : I) → ℕ → Dusk.Grain (w t)) :
    PhysicalWalsh.TapeTask (fieldVolume P B w) (fieldVolume P B w)
      (fun t => Code.send (fieldHeader P B w t,(List.range (P t*4*B t)).map (Dusk.mark ∘ r t)))
      (fun t => Code.send (fieldHeader P B w t,(List.range (P t*4*B t)).map (Dusk.mark ∘ storedAt (B t) (r t)))) :=
  (ordinalStoredBounded P B w r).release

end
end PhysicalWalshBase

end NearSquareRoot
end Computability
end OAI
