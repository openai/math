import OAI.Hierarchy.ExcludedCubeExpanders
import OAI.ThreeFlat.Diagonal.BlockDegreeSchedule
import OAI.ThreeFlat.Diagonal.ShrinkTable
import OAI.ThreeFlat.Diagonal.RefreshFixedGrid

namespace OAI
/-! # Fixed shrink and refresh tables from cofinally many expander orders -/

noncomputable section
namespace Hierarchy.TraceDistribution

open ThreeFlat LinearAlgebra.SpectralBooks
open Diagonal Expander
open scoped BigOperators Classical

/-- The degrees and the two genuine tensor-map tables used by one compression block.
The final shrink size is chosen among the orders actually available in the family. -/
structure CompressionBlock (F : Type) [Field F] where
  levels : ℕ
  positive : 0 < levels
  exponent : ℕ → ℕ
  shrink : ShrinkMotif.Table F
  small : ∀ i, ((2^(2*(2^exponent i)+1)*(2^exponent i)*(2^exponent i):ℕ):ℝ) /
    2^exponent (i+1) ≤ 1/1024
  h : ℕ
  pad : ℕ
  γ : ℝ
  G : NonlinearExpanders.Graph (exponent levels) h
  degree_pos : 0<h
  order_ge : 2 ≤ 2^exponent levels
  real_bound : Bound (transition G.arcs h) ℝ γ
  restore : 1+h+pad=2^exponent 0
  refresh : RefreshMotif.Table F G.arcs (1+h+pad) (RefreshMotif.leading h (1+h+pad) γ+1)
  contracts : ((1+h+pad:ℕ) + 2*(RefreshMotif.leading h (1+h+pad) γ+1):ℝ) *
    (126/127:ℝ)^levels ≤ 1/4

theorem compressionBlock_of_expanders {F : Type} [Field F] (fam : NonlinearExpanders.SpectralFamily F) :
    Nonempty (CompressionBlock F) := by
  obtain ⟨h,γ,hh,hγ,graphs⟩ := fam
  let next (a : ℕ) := (graphs (shrinkThreshold (2^a))).choose
  have bound (a : ℕ) : shrinkThreshold (2^a) ≤ next a := (graphs _).choose_spec.1
  let x : ℕ → ℕ := Nat.rec (degreeIndex 2 h 0+1) (fun _ a => next a)
  have xzero : 2^x 0=blockDegree 2 h 0 := by simp [x,blockDegree,pow_succ,Nat.mul_comm]
  have grows (i : ℕ) : shrinkThreshold (2^x i) ≤ 2^x (i+1) :=
    (bound (x i)).trans (Nat.lt_two_pow_self.le)
  have small (i : ℕ) :
      ((2^(2*(2^x i)+1)*(2^x i)*(2^x i):ℕ):ℝ)/2^x (i+1) ≤ 1/1024 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    have le := grows i
    unfold shrinkThreshold at le
    rw [one_mul,mul_comm]
    exact_mod_cast le
  obtain ⟨s,hs,loss⟩ := choose_block_length (q:=2) (by decide) hh hγ
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  obtain ⟨G,realBound,spectral⟩ := (graphs (shrinkThreshold (2^x j))).choose_spec.2
  let pad := blockDegree 2 h 0 - (1+h)
  have restore : 1+h+pad=blockDegree 2 h 0 := by
    have := degree_start (q:=2) (by decide) h
    dsimp [pad]
    omega
  have two : 2≤2^x (j+1) := by
    apply le_trans _ (grows j)
    unfold shrinkThreshold
    have : 0 < 2^(2*(2^x j)+1)*(2^x j)*(2^x j) := by positivity
    omega
  exact ⟨⟨j+1,by omega,x,(ShrinkMotif.exists_table F).some,small,h,pad,γ,G,hh,two,realBound,
    restore.trans xzero.symm,
    (RefreshMotif.exists_table F (by positivity) hh (by omega) G.arcs hγ spectral).some,
    by simpa only [restore,RefreshMotif.leading] using loss⟩⟩

/-- Under the geometric contradiction hypothesis, the necessary expander and
both tensor-map tables are produced over the field itself, in arbitrary dimension. -/
theorem compressionBlock_of_missing {F : Type} [Field F] {d : ℕ}
    (large : 2≤d) (missing : ¬HasSpectralFlat F d) : Nonempty (CompressionBlock F) :=
  compressionBlock_of_expanders (NonlinearExpanders.family_of_missing NonlinearExpanders.excluded_cube large missing)


end Hierarchy.TraceDistribution

end
end OAI
