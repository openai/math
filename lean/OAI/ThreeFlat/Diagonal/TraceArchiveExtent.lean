import OAI.ThreeFlat.Diagonal.TraceArchiveSource

namespace OAI
/-! # Bounding every node offset by the actual chronological heap usage -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open RAM RAM.NavigationNodeRows NavigationDirectory

theorem node_counts_heap (ops : List Stage) :
    (ops.map Stage.nodes).sum+(ops.map successors).sum≤(ops.map Stage.heapWords).sum := by
  have localSize (s : Stage) : s.nodes+successors s ≤ s.heapWords := by
    cases s with
    | shrink x =>
      change x.originalSites+x.outputSites ≤ 15*x.motifs+8*x.oldEdges+2*x.oldBase+7*x.newEdges+
        x.newEdges*x.residual+2+(7+6*x.localCapacity+8*x.newDegree)*x.outputSites+2*x.originalSites
      have h : x.outputSites≤(7+6*x.localCapacity+8*x.newDegree)*x.outputSites :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    | refresh v m l h p =>
      let n := RefreshStageLayout.counts v m l h p
      change n.nodes+n.nodes≤n.choiceSpan+n.sparseSpan+n.splitSpan+n.graphSpan+n.newWidthSpan+
        (15+8*(1+h+p))*n.nodes
      have enough := Nat.mul_le_mul_right n.nodes (show 2≤15+8*(1+h+p) by omega)
      omega
  induction ops with
  | nil => exact le_rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons]; have := localSize x;omega

/-- A single size bound covers both charge columns and all eight fields of each journal node. -/
theorem actual_span (K : ℕ) (ops : List Stage) (c : Cursor) (s : Layer) (start : s.first=c.node)
    (q : Layers) (mem : q∈nodeLayers K ops c s) :
    q.actual.first+q.actual.count≤c.node+s.count+(ops.map Stage.heapWords).sum :=
  (TraceRecovery.node_room K ops c s start q mem).trans (by have := node_counts_heap ops;omega)

end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
