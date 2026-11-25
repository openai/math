import OAI.Hierarchy.ProbeDiscrepancy
import OAI.Hierarchy.ProbeStripThreshold
import OAI.Hierarchy.ProbePaddedFailure

namespace OAI
/-! # A single public density lower bound for all failed native strip tests -/

namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical
noncomputable section
variable {E A : Type*} [Fintype E] [Nonempty E] [Fintype A] {k : ℕ} [Nonempty (Fin k)]

/-- The zero-scale spectral trial has no positive option violations. Its only
remaining errors are the absolute demand prices. -/
theorem discrepancy_ceiling (F : Type*) [Field F] (edge : E→Chord k) (req : A→E) (value : E→ℝ) {C : ℝ}
    (hC : 0≤C) (positive : ∀e,0≤value e) (cap : ∀a,value (req a)≤C) : discrepancy F edge req value≤C := by
  let e := edge (Classical.arbitrary E)
  let : Nontrivial (Fin k) := ⟨e.1.1,e.1.2,e.2.ne⟩
  let φ := (spectrum_nonempty.{0} (Fin k) F).to_subtype.some
  refine (discrepancy_le F edge req value φ (le_rfl : (0:ℝ)≤0)).trans ?_
  apply Finset.sup'_le
  intro i _
  rcases i with e | a
  · change max 0 (0*distance φ (edge e)-value e)≤C
    simp only [zero_mul,zero_sub]
    exact max_le hC ((neg_nonpos.mpr (positive e)).trans hC)
  · change |0*distance φ (edge (req a))-value (req a)|≤C
    simpa only [zero_mul,zero_sub,abs_neg,abs_of_nonneg (positive _)] using cap a

/-- Downward rounding in the gap ROM preserves this uniform upper bound at
one real read word; masks can also emit zero on a dormant original ordinal. -/
theorem quantized_ceiling {C x : ℝ} {q : ℕ} (width : 0<q) (pos : 0≤x) (cap : x≤C) :
    (⌊(q:ℝ)*x⌋₊:ℝ)/q≤C := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr width)).mpr
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  calc
    (⌊(q : ℝ) * x⌋₊ : ℝ) ≤ (q : ℝ) * x := Nat.floor_le (mul_nonneg hq pos)
    _ ≤ (q : ℝ) * C := mul_le_mul_of_nonneg_left cap hq
    _ = C * (q : ℝ) := mul_comm _ _

/-- The high global sum from the real failure scanner implies the fraction used
in the public clock, at the exact native integer price precision. -/
theorem density_of_count {ε C : ℝ} {n count : ℕ} (he : 0≤ε) (hc : 0≤C)
    (measured : 2*ε*n≤(count:ℝ)*C) : ε/(C+1)*n≤count := by
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by linarith : 0<C+1)).2
  have nn := mul_nonneg he (Nat.cast_nonneg n)
  have used : 0≤(count:ℝ) := Nat.cast_nonneg count
  nlinarith

/-- A single public fraction covers both the true and padded gate tables, even
if they have different lengths. All sites outside the original support read zero. -/
theorem padded_repair_share {V : Type*} [Fintype V] (word : V→ℕ) (trueVal : V→ℝ) (live : Finset V)
    {Q n : ℕ} {C ε : ℝ} (he : 0<ε) (hQ : 0<Q) (hC : 0≤C) (small : live.card≤n)
    (off : ∀i∉live,word i=0) (cap : ∀i,(word i:ℝ)/Q≤C) (rounded : ∀i∈live,|(word i:ℝ)/Q-trueVal i|≤ε)
    (flag : 4*ε*n*Q≤∑i,(word i:ℝ)) :
    ε/(C+1)*n≤(AdaptiveProbe.paddedFailed word (ε:=ε) Q).card ∧
      ∀i∈AdaptiveProbe.paddedFailed word (ε:=ε) Q,i∈live ∧ ε<trueVal i := by
  obtain ⟨many,real⟩ := AdaptiveProbe.padded_failed_count live word trueVal he hQ hC small off cap rounded flag
  exact ⟨density_of_count he.le hC many,real⟩

end
end Hierarchy.Probe

end OAI
