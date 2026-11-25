import OAI.Computability.BorderVNP.PackedSelectedEpochNodeFrames

/-! # Verified gates and guessed bits of all selected combining stages

The same Boolean frames carry the measured source receipts, check their
physical histogram words and meet the per-rectangle budget. Each of their
occurrences in the entire rooted history is charged at its actual level.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Epoch Shortening Shortening.Adaptive Packing Diagonal Filter TeamScales
open scoped Classical BorderVNP.Epoch.Cube

universe u v
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- Actual source node family at one level of the outer copy tree. -/
noncomputable abbrev Nodes (start t w : ℕ) :=
  let high := S.high (EnrichedOuter.offset S start t)
  ∀ i : Fin S.rounds, S.source.Node S.last high (fun j => (before S start t j).sites)
    (fun j => (before S start t j).edges) w S.fanIn i

/-- Cost of a physical combining kernel using the very pins read by the
normalized execution, including all child conjunctions and guessed bits. -/
noncomputable def kernelWork {start t w : ℕ} (nodes : Nodes S start t w) (i : Fin S.rounds) :=
  let high := S.high (EnrichedOuter.offset S start t)
  let steps := S.source.namedKernels S.last high (fun j => (before S start t j).sites)
    (fun j => (before S start t j).edges) w nodes
  (steps i.val i.isLt).size + (2*S.fanIn+4) + Fintype.card (EnrichedOuter.Count S start t (fun _ => w) i.val)

/-- Express the charged gates and input bits on the source path's native pins. -/
theorem kernelWork_native {start t w : ℕ} (nodes : Nodes S start t w) (i : Fin S.rounds) :
    kernelWork S nodes i = (nodes i).size + (2*S.fanIn+4) + Fintype.card (PublicDenseReceipt.Words
      (PublicDenseReceipt.Seed (S.source.pattern i).bins (S.level (EnrichedOuter.offset S start t) (i.val+1))) e.count w) := by
  dsimp only [kernelWork]
  rw [SourcePath.namedKernels_size]
  congr 1
  exact (Fintype.card_congr (Physical.pinEquiv (I := Cube D) (e := e)
    (B := fun i => (S.source.pattern i).bins.Bin) (depth := S.level (EnrichedOuter.offset S start t)) (fun _ => w) i)).symm

/-- The source-correct family is compiled at every actual epoch and kept
unchanged when its gate, guard and guess costs are charged. Uniformly in
processor count, its complete tree of combining nodes uses strictly fewer
than r times n to the power 0.915 operations and guess pins. -/
theorem eventually_selected_receipt_work (hm : 0 < m) {a x : ℕ} (s : EpochScales S a x) :
    ∃ C p : ℕ, ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ) ≤ 2^((n:ℝ)^ω) →
      let T := epochs s.τ n
      let start := CoverScale.initialDepth (Cube D) r n
      let w := 60*logWidth r n
      ∀ (P : Fin T → Type) (bits : ∀ t, P t → ℕ),
        ∃ nodes : ∀ t : Fin T, Nodes S start t w,
          (∀ (t : Fin T) (i : Fin S.rounds),
            let high := S.high (EnrichedOuter.offset S start t)
            SourceTemplate.NodeRun.{u,v} (P := Port S.fanIn (P t) i.val) (bits := width (bits t) S.fanIn i.val)
              (S.source.pattern i) (S.source.stepDepth S.last high i) S.positiveFanIn (S.source.catalog (i.val+1))
              ((2*n*r)^2) (nodes t i)) ∧
          (∀ t i, kernelWork S (nodes t) i ≤ rowWork C (CoverScale.sites (Cube D) start)
            (logWidth r n) p ((before S start t i).parallel S.fanIn)) ∧
          (treeWork S.fanIn S.rounds T (fun t i => kernelWork S (nodes t) i):ℝ) < r*(n:ℝ)^(915/1000:ℝ) := by
  obtain ⟨C,p,compile⟩ := eventually_epoch_nodes.{u,v} S hm s
  obtain ⟨ω,hω,budget⟩ := eventually_treeWork S s C p
  refine ⟨C,p,ω,hω,?_⟩
  filter_upwards [compile,budget,eventually_ranges S s (fun _ => 0) (fun _ => 0)] with n frames charge ranges
  intro r hr hrmax T start w P bits
  choose nodes sem cost using fun t : Fin T => frames r hr t t.isLt (P := P t) (bits := bits t)
  have measured (t : Fin T) (i : Fin S.rounds) : kernelWork S (nodes t) i ≤ rowWork C
      (CoverScale.sites (Cube D) start) (logWidth r n) p ((before S start t i).parallel S.fanIn) :=
    (kernelWork_native S (nodes t) i).le.trans (cost t i)
  exact ⟨nodes,sem,measured,charge r hr hrmax (ranges r hr).1 _ measured⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
