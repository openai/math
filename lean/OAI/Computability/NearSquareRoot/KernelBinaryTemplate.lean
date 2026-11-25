import OAI.Computability.NearSquareRoot.KernelPassCorrectedBatch
import OAI.Computability.NearSquareRoot.KernelPassSaving
import OAI.Computability.NearSquareRoot.KernelFrequencyStage

/-! # Fixed normalized binary Walsh templates with strict call savings

The retained program has literal finite dyadic tables and the same instructions
at every even child width. The rational finite-word checker makes the template
choice executable for rational exponents. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open BinaryQuery KernelPassSaving OAI.LinearAlgebra.FiniteFourier Rect.Binary
open scoped CyclotomicCode

private theorem corrected_stage {L b m N : ℕ} (S : System L b)
    (hN : N = labels L b) (hm : 2 ≤ m) (hodd : m ≡ 1 [MOD 2]) (e : Label L b ≃ Fin N)
    (p : Plan (Arity m (S.D-1)) (N*Plan.basisWidth m) (N*Plan.basisWidth m))
    (hp : ∀ h v (x : Bank (Arity m (S.D-1)) h (N*Plan.basisWidth m))
      (y : Addr (Arity m (S.D-1)) h),
      Plan.labelSlice e v y (p.applyAt h x) =
        (Plan.stageMatrix hm (∑ j, BinaryQuery.test m (S.D-1) (y j))).mulVec (Plan.labelSlice e v y x))
    (hc : p.calls ≤ stageBound L b m S.D) :
    ∃ t : Plan (axes m S.D) (labels L b * expandedWidth m) (labels L b * expandedWidth m),
      Correct t ∧ ∃ stage, stage ≤ stageBound L b m S.D ∧ t.calls ≤ callBound L b m S.D stage := by
  subst N
  have hd := S.dimension_pos
  have hA : axes m S.D = Arity m (S.D-1) := by unfold Arity axes; omega
  rw [hA]
  refine ⟨Plan.correctedLabelBatch hm e p, Plan.correctedLabelBatch_correct hm hodd e p hp,
    p.calls,hc,?_⟩
  rw [Plan.calls_correctedLabelBatch, callBound, hA]

/-- Compile the physical pencil and all independent repair rows to one plan.
Every call and each fixed signed table is part of the resulting syntax. -/
theorem compiled_system {L b m : ℕ} (S : System L b) (hm : 2 ≤ m) (hodd : m ≡ 1 [MOD 2]) :
    ∃ t : Plan (axes m S.D) (labels L b * expandedWidth m) (labels L b * expandedWidth m),
      Correct t ∧ ∃ stage, stage ≤ stageBound L b m S.D ∧ t.calls ≤ callBound L b m S.D stage := by
  cases m with
  | zero => omega
  | succ m =>
    let e := labelIndex L b
    exact corrected_stage S rfl hm hodd e (generatedStage S hm e)
      (fun _ => generatedStage_frequency S hm e) (generatedStage_calls S hm e)

/-- The normalized binary template of the call-saving construction. A single
finite restricted program realizes the target at every even child width. -/
theorem exists_normalized_template {θ : ℝ} (hθ : 1/2 < θ) :
    ∃ t : Candidate, 5 ≤ t.arity ∧ 2 ≤ t.rows ∧ Correct t.program ∧
      (t.program.calls : ℝ) / t.rows < (t.arity : ℝ)^θ := by
  obtain ⟨L,b,m,_,_,hm,hodd,S,hA,hW,hcost⟩ := exists_system hθ
  obtain ⟨p,hp,stage,hs,hc⟩ := compiled_system S hm hodd
  exact ⟨⟨_,_,p⟩,hA,hW,hp,hcost stage p.calls hs hc⟩

theorem exists_good_template {num den : ℕ} (hθ : 1/2 < (num : ℝ)/den) :
    ∃ t : Candidate, t.Good num den := exists_normalized_template hθ

/-- Executably select the first certified finite instruction program for
a rational exponent above a half. The existence proof is erased by evaluation. -/
def binaryTemplate (num den : ℕ) (hθ : 1/2 < (num : ℝ)/den) : Candidate :=
  Candidate.find num den (by
    by_contra! hz
    have hz' : den = 0 := by omega
    norm_num [hz'] at hθ) (exists_good_template hθ)

theorem binaryTemplate_good (num den : ℕ) (hθ : 1/2 < (num : ℝ)/den) :
    (binaryTemplate num den hθ).Good num den := Candidate.find_good _ _

end KernelPass

end NearSquareRoot
end Computability
end OAI
