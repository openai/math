import OAI.Optimization.LinearProgramming.Compression.PublicTransport

/-! Public output sizes and prefix-extension guarantees for any native generator policy
with the paper's simultaneous-assignment invariant. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.OracleSpec

/-- A finite generator policy can be supplied an equivalent public request type without
changing any of its bounds or observable values. -/
theorem serviceEvents_pullback_contract {α β : Type} [DecidableEq α] [DecidableEq β] [Fintype β]
    (e : α ≃ β) (n : ℕ) (proxy logs : β → ℝ) (req : MinorRequest β)
    (hr : RestartTest proxy req)
    (hl : ∀ J : Finset β, IsDissociated proxy J → ∃ f : β → ℚ,
      ValidMinorAssignment n logs f ∧ ∀ i q, req J i = some q → f i = q)
    (us : List α) :
    let p := onlineMinorBitPolynomial.eval n
    let events := serviceEventsFrom (pullbackMinorRequest e req) RequestTrace.start us
    (∀ u q, (u,some q) ∈ events → RAM.ratBits q ≤ 3+2*p) ∧
      ∀ j, MinorLog.extension n p (fun i ↦ logs (e i)) (events.take j) := by
  let proxy' := fun i : α ↦ proxy (e i)
  have htest : RestartTest proxy' (pullbackMinorRequest e req) := hr.pullback e
  have hwidth (J : Finset α) (hJ : IsDissociated proxy' J) := hl (J.map e.toEmbedding)
    ((isDissociated_map_iff proxy e.toEmbedding J).mpr hJ)
  have hzero : IsDissociated proxy' ∅ := by
    intro A hA B hB hne
    exact (hne ((Finset.subset_empty.mp hA).trans (Finset.subset_empty.mp hB).symm)).elim
  constructor
  · apply serviceEventsFrom_outputBits htest _ _ _ hzero us
    intro J hJ u q hq
    obtain ⟨f, hf, agree⟩ := hwidth J hJ
    obtain ⟨_, hnum, hden⟩ := hf.1 (e u)
    rw [agree (e u) q hq] at hnum hden
    have logBound {a b : ℕ} (h : a ≤ 2^b) : a.log2 ≤ b := by
      rcases eq_or_ne a 0 with rfl | ha
      · simp
      · exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ((Nat.log2_self_le ha).trans h)
    have hn := logBound hnum
    have hd := logBound hden
    unfold RAM.ratBits; omega
  · intro j
    apply serviceEvents_extensions _ proxy' (fun i ↦ logs (e i)) htest _ _ _ us j
    intro J hJ
    obtain ⟨f, hf, agree⟩ := hwidth J hJ
    obtain ⟨hsize, hclip⟩ := validMinorAssignment_pullback e hf
    exact ⟨fun i ↦ f (e i), hsize, hclip, fun i q hi ↦ agree (e i) q hi⟩

end Compression
end LinearProgramming
end Optimization
end OAI
