import OAI.Computability.BorderVNP.CubePhysicalPublicContraction
import OAI.Computability.BorderVNP.DiagonalCommonAdvice
import OAI.Computability.BorderVNP.TeamScales

/-! # A prime-field cube selected before any possible small border circuit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Cube Cube.Physical VPVNP MvPolynomial

/-- The one fixed cube used in every length of the stretch argument. Its table
positions, packet widths, selection cost and budget for every product alphabet
are all chosen over the original prime field. -/
structure FixedCube (K : Type*) [Field K] where
  /-- Logarithm of the fixed cube dimension. -/
  power : ℕ
  /-- Predecessor of the cube dimension, used to index its antipodal pairs. -/
  pred : ℕ
  dimension : pred+1 = 2^power
  /-- Selector fraction allowed in the physical cut budget. -/
  tolerance : ℝ
  positive : 0 < tolerance
  scale : 100*(2*((2 : ℝ)^power)^(-1/2 : ℝ)+tolerance) < 1/10^6
  /-- Number of target bits per wire in one copy. -/
  b : ℕ
  /-- Number of selected profiles per block. -/
  h : ℕ
  /-- Multiplicity of the ordinary tensor sum. -/
  copies : ℕ
  /-- Width assigned to one selected oriented edge. -/
  width : ℕ
  block_pos : 0 < h*b
  copies_pos : 1 ≤ copies
  /-- Scalar at each local matrix position of the fixed cube. -/
  table : TableEntry pred b h copies width → K
  valid : ValidTables table
  cost : ∀ d blocks : ℕ, 0 < d → ∀ select : Packet pred d blocks → Selector pred copies h,
    (cutWidth b width select (chosen b width select) : ℝ) +
      ∑ _p : Packet pred d blocks, (MotifWidths.selectorBits copies (Fintype.card (Edge (pred+1))) h : ℝ) ≤
      padded pred d blocks (h*b) * (2/Real.sqrt (pred+1) + (pred+1)/d + tolerance)

/-- The cube can be selected at any prescribed minimum width. -/
theorem exists_fixedCube (K : Type*) [Field K] (minimum : ℕ) :
    ∃ cube : FixedCube K, minimum ≤ cube.h*cube.b := by
  obtain ⟨power,η,hη,hscale⟩ := TeamScales.exists_cube_dimension
  let pred := 2^power-1
  have hd : pred+1 = 2^power := Nat.sub_add_cancel Nat.one_le_two_pow
  obtain ⟨b,h,copies,width,hmin,hpos,hcopies,table,valid,cost⟩ :=
    exists_physical_tables K pred minimum η hη
  exact ⟨⟨power,pred,hd,η,hη,hscale,b,h,copies,width,hpos,hcopies,table,valid,cost⟩,hmin⟩

/-- Scalar extension to the field containing the fixed shortening preserves the
same tuple of actual cube matrices. -/
theorem FixedCube.extend_valid {K F : Type*} [Field K] [Field F] (cube : FixedCube K) (f : K →+* F) :
    ValidTables (f ∘ cube.table) := by
  apply cube.valid.specialize
  intro z hz
  have h := congrArg f hz
  rw [map_zero] at h
  have hf : f.comp (Int.castRingHom K) = Int.castRingHom F := Subsingleton.elim _ _
  simpa only [map_eval₂Hom, hf, Function.comp_def] using h

/-- In the finite branch field both the fixed shortening and every actual cube
entry have the jointly specialized values, independently of the later layout. -/
theorem FixedCube.chart_valid {K F : Type*} [Field K] [Field F] (cube : FixedCube K) (f : K →+* F)
    {D m q k s : ℕ} {G : Crossing.PaidIdentity F D m}
    {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {R : CommonField G (f ∘ cube.table) q k s ord} (chart : AdvisedBranch R) :
    ValidTables (fun i => algebraMap R.E₀ chart.E (R.entry (Sum.inr i))) :=
  chart.cube_tables (cube.extend_valid f)

end Diagonal

end BorderVNP
end Computability
end OAI
