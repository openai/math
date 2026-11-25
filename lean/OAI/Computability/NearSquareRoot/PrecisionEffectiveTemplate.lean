import OAI.Computability.NearSquareRoot.KernelUniformBinaryTemplate
import OAI.Computability.NearSquareRoot.PrecisionEffectiveCutoff
import OAI.Computability.NearSquareRoot.PrecisionEffectiveFactor

/-! # Working precision for the actual templates selected by uniform search

The address width threshold is evaluated on the raw opcode list, including
its literal signed coefficients. It thereby supplies one computable function
of the scheduler index for the entire family of selected templates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax

open PhysicalWalshNode PhysicalWalsh.Pieces

def rawPrecisionCutoff (r : Raw) : ℕ := precisionCutoff (rawFactor r)

theorem rawPrecisionCutoff_primrec : Primrec rawPrecisionCutoff :=
  precisionCutoff_primrec.comp rawFactor_primrec

/-- The raw syntax decodes to this very square program. Both its call saving
and its numerical certificate hold for the same program. -/
def AccurateTemplate (num den K : ℕ) (r : Raw) : Prop :=
  ∃ (a W : ℕ) (ha : 1 < a+1) (hw : 0 < W) (p : Plan (a+1) W W),
    r.1 = a+1 ∧ Packed.decode (a+1) r.2 = ⟨W,W,p⟩ ∧
    interpreted r = ⟨a+1,W,p⟩ ∧ Correct p ∧
    (p.calls : ℝ)/W < ((a+1 : ℕ) : ℝ)^((num : ℝ)/den) ∧
    ∀ k ≥ K, GroupedAccurateAt ha hw p k

theorem accurateTemplate_of_good {num den : ℕ} (r : Raw) (h : (interpreted r).Good num den) :
    AccurateTemplate num den (rawPrecisionCutoff r) r := by
  obtain ⟨A,ops⟩ := r
  cases A with
  | zero =>
    generalize hP : Packed.decode 0 ops = t
    obtain ⟨i,o,p⟩ := t
    by_cases he : o = i
    · subst o
      simp [interpreted,hP,Candidate.Good] at h
    · simp [interpreted,hP,packedCandidate,he,Candidate.Good] at h
  | succ a =>
    generalize hP : Packed.decode (a+1) ops = t
    obtain ⟨i,o,p⟩ := t
    by_cases he : o = i
    · subst o
      have hi : interpreted (a+1,ops) = ⟨a+1,i,p⟩ := by simp [interpreted,hP]
      rw [hi] at h
      obtain ⟨hA,hW,hp,hcalls⟩ := h
      change 5 ≤ a+1 at hA
      change 2 ≤ i at hW
      have ha : 1 < a+1 := by omega
      have hw : 0 < i := by omega
      refine ⟨a,i,ha,hw,p,rfl,hP,hi,hp,hcalls,?_⟩
      exact fun _ hk => grouped_accurate_of_cutoff ha hw p hp (recursionFactor_le_rawFactor ops p hP) hk
    · simp [interpreted,hP,packedCandidate,he,Candidate.Good] at h

/-- Uniform template selection computes the working-range threshold together
with the template, independently of the multiplication input. -/
theorem computable_midpoint_precision :
    ∃ (select : ℕ → Raw) (K : ℕ → ℕ), Computable select ∧ Computable K ∧
      (∀ j, K j = rawPrecisionCutoff (select j)) ∧
      ∀ j, AccurateTemplate (j+3) (2*(j+2)) (K j) (select j) := by
  obtain ⟨s,hs,hgood⟩ := computable_midpoint_templates
  exact ⟨s,rawPrecisionCutoff ∘ s,hs,rawPrecisionCutoff_primrec.to_comp.comp hs,fun _ => rfl,
    fun j => accurateTemplate_of_good _ (hgood j)⟩

end KernelPass.ComputableSyntax

end NearSquareRoot
end Computability
end OAI
