import OAI.Computability.NearSquareRoot.KernelCyclotomicCode
import OAI.Computability.NearSquareRoot.KernelRepair
import Mathlib.LinearAlgebra.Pi

/-! # Finite exact search for the binary Hermite correction table

A table passes a finite matrix test over the dyadic cyclotomic coefficient
ring. The test depends only on the sign pattern and its predictor values.
The sparse Vandermonde proof supplies termination of the search even when
the winning table is very large. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RepairSearch

open OAI.LinearAlgebra.FiniteFourier Matrix
open scoped CyclotomicCode

variable {R : Type*} [CommRing R] {W s : ℕ}

abbrev CheckIndex (s : ℕ) := Fin s ⊕ Fin s
abbrev Table (R : Type*) (s : ℕ) := Matrix (CheckIndex s) (CheckIndex s) R

/-- Gather the predicted and original syndromes. -/
def gather (p : Fin W → R) (H : Matrix (Fin s) (Fin W) R) :
    Matrix (CheckIndex s) (Fin W) R :=
  fun c w => Sum.elim (fun i => H i w * p w) (fun i => H i w) c

/-- Subtract the predicted correction, then add the corrected target. -/
def scatter (p : Fin W → R) (H : Matrix (Fin s) (Fin W) R) :
    Matrix (Fin W) (CheckIndex s) R :=
  fun w => Sum.elim (fun i => -p w * H i w) (fun i => H i w)

theorem gather_mulVec (p : Fin W → R) (H : Matrix (Fin s) (Fin W) R) (x : Fin W → R) :
    gather p H *ᵥ x = Sum.elim (H *ᵥ (p * x)) (H *ᵥ x) := by
  funext c
  cases c with
  | inl i => simp [gather, Matrix.mulVec, dotProduct, mul_assoc]
  | inr i => rfl

theorem scatter_mulVec (p : Fin W → R) (H : Matrix (Fin s) (Fin W) R)
    (x : CheckIndex s → R) (i : Fin W) :
    (scatter p H *ᵥ x) i = -p i * (Hᵀ *ᵥ x ∘ Sum.inl) i + (Hᵀ *ᵥ x ∘ Sum.inr) i := by
  simp [scatter, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Finset.mul_sum,
    mul_assoc]

/-- The discrepancy compensated by the table at one frequency. -/
def discrepancy (u z : R) (p : Fin W → R) : Matrix (Fin W) (Fin W) R :=
  diagonal (fun i => z - (p i - u * (p i ^ 3 - p i)))

/-- Encode the Hermite identity as a single matrix equation. This is a
finite condition on the table entries, independent of the input rows. -/
theorem exists_certificate {u z : R} (hu : u * (2 : R) = 1) (hz : z ^ 2 = 1)
    (p : Fin W → R) (nodes : Fin W → R) (hnodes : Pairwise fun i j => IsUnit (nodes i - nodes j))
    (J : Finset (Fin W)) (hj : J.card ≤ s) (hok : ∀ i ∉ J, p i = z) :
    ∃ t : Table R s, scatter p (repairCheck nodes s) * t * gather p (repairCheck nodes s) =
      discrepancy u z p := by
  have hu' : u * ((2 : ℕ) : R) = 1 := by simpa using hu
  obtain ⟨T, hT⟩ := exists_fullRateHermiteRepair nodes hnodes hu' (fun _ : Unit => z)
    (fun _ => hz) (fun _ => p) (fun _ => J) (fun _ => hj) (fun _ => hok)
  let e := LinearEquiv.sumArrowLequivProdArrow (Fin s) (Fin s) R R
  let M := e.symm.toLinearMap.comp ((T ()).comp e.toLinearMap)
  refine ⟨LinearMap.toMatrix' M, Matrix.ext_iff_mulVec.mpr ?_⟩
  intro x
  rw [← mulVec_mulVec, ← mulVec_mulVec, gather_mulVec, LinearMap.toMatrix'_mulVec]
  funext i
  rw [scatter_mulVec, discrepancy, Matrix.mulVec_diagonal]
  have h := hT () x i
  dsimp only at h
  let H := repairCheck nodes s
  let t := T () (H *ᵥ (p * x), H *ᵥ x)
  change -p i * (Hᵀ *ᵥ t.1) i + (Hᵀ *ᵥ t.2) i = _ * x i
  change (p i - u * (p i^3 - p i)) * x i - p i * (Hᵀ *ᵥ t.1) i + (Hᵀ *ᵥ t.2) i = z * x i at h
  linear_combination h

open CyclotomicCode in
private instance tableEnc {a s : ℕ} : Encodable (Table (Number a) s) :=
  inferInstanceAs (Encodable (CheckIndex s → CheckIndex s → Number a))

open CyclotomicCode in
/-- Enumerate dyadic coefficient matrices until the equation holds. The search
does not inspect any data from the transform being computed. -/
def table {a W s : ℕ} (hW : W ≤ 2^(a+1)) (z : Number a) (hz : z ^ 2 = 1)
    (p : Fin W → Number a) (J : Finset (Fin W)) (hj : J.card ≤ s)
    (hok : ∀ i ∉ J, p i = z) : Table (Number a) s :=
  let nodes := fun i : Fin W => Number.generator a ^ i.val
  Encodable.choose (exists_certificate Number.half_two hz p nodes
    (Number.node_differences hW) J hj hok)

open CyclotomicCode in
theorem table_correct {a W s : ℕ} (hW : W ≤ 2^(a+1)) (z : Number a) (hz : z ^ 2 = 1)
    (p : Fin W → Number a) (J : Finset (Fin W)) (hj : J.card ≤ s)
    (hok : ∀ i ∉ J, p i = z) :
    let H := repairCheck (fun i : Fin W => Number.generator a ^ i.val) s
    scatter p H * table hW z hz p J hj hok * gather p H = discrepancy (Number.half a) z p :=
  by exact Encodable.choose_spec (p := fun t => scatter _ _ * t * gather _ _ = discrepancy _ _ _) _

/-- Apply a finite matrix to the concatenated input blocks, then split its
output back into two blocks for the ordinary inverse conversions. -/
def applyTable (t : Table R s) :
    ((Fin s → R) × (Fin s → R)) →ₗ[R] ((Fin s → R) × (Fin s → R)) :=
  let e := LinearEquiv.sumArrowLequivProdArrow (Fin s) (Fin s) R R
  e.toLinearMap.comp (t.mulVecLin.comp e.symm.toLinearMap)

/-- Passing the matrix test suffices for the full-rate Hermite formula at
every choice of input coordinates. -/
theorem certificate_action {u z : R} {p : Fin W → R} {H : Matrix (Fin s) (Fin W) R}
    {t : Table R s} (ht : scatter p H * t * gather p H = discrepancy u z p)
    (x : Fin W → R) (i : Fin W) :
    let y := applyTable t (H *ᵥ (p * x), H *ᵥ x)
    (p i - u * (p i ^ 3 - p i)) * x i - p i * (Hᵀ *ᵥ y.1) i + (Hᵀ *ᵥ y.2) i = z * x i := by
  have h := congrFun (Matrix.ext_iff_mulVec.mp ht x) i
  rw [← mulVec_mulVec, ← mulVec_mulVec, gather_mulVec, scatter_mulVec,
    discrepancy, Matrix.mulVec_diagonal] at h
  let y := applyTable t (H *ᵥ (p * x), H *ᵥ x)
  change -p i * (Hᵀ *ᵥ y.1) i + (Hᵀ *ᵥ y.2) i = _ * x i at h
  change (p i - u * (p i ^ 3 - p i)) * x i - p i * (Hᵀ *ᵥ y.1) i + (Hᵀ *ᵥ y.2) i = z * x i
  linear_combination h

open CyclotomicCode in
/-- The computed table repairs all the original rows. The same matrices can
be reused on every array length with the specified finite sign signatures. -/
theorem repaired_program {a W s m : ℕ} (hW : W ≤ 2^(a+1))
    (z : (Fin m → ZMod 2) → Number a) (hz : ∀ k, z k ^ 2 = 1)
    (p : (Fin m → ZMod 2) → Fin W → Number a)
    (J : (Fin m → ZMod 2) → Finset (Fin W)) (hj : ∀ k, (J k).card ≤ s)
    (hok : ∀ k i, i ∉ J k → p k i = z k)
    {V ν : Type*} [AddCommGroup V] [Module (Number a) V] (S : V ≃ₗ[Number a] (ν → Number a))
    (sig : ν → Fin m → ZMod 2) (P : (Fin W → V) → Fin W → V)
    (hP : ∀ x i v, S (P x i) v = p (sig v) i * S (x i) v)
    (x : Fin W → V) (i : Fin W) :
    hermiteRepairProgram 2 (Number.half a) P S
      (repairCheck (fun i : Fin W => Number.generator a ^ i.val) s)
      ((fun k => applyTable (table hW (z k) (hz k) (p k) (J k) (hj k) (hok k))) ∘ sig) x i =
        S.symm ((z ∘ sig) * S (x i)) :=
  KernelRepair.signature_table_correct (Number.half a) z p _ _
    (fun k => certificate_action (table_correct hW (z k) (hz k) (p k) (J k) (hj k) (hok k)))
    S sig P hP x i

end RepairSearch

end NearSquareRoot
end Computability
end OAI
