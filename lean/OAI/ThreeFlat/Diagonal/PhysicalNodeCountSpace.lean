import OAI.ThreeFlat.Diagonal.NavigationNodeArchive
import OAI.ThreeFlat.Diagonal.PhysicalRegisterSpace

namespace OAI
/-! # Node ordinals of the actual cursor history -/

namespace ThreeFlat.Diagonal.NavigationPass

open NavigationDirectory PhysicalStage RAM.NavigationNodeRows
noncomputable section

/-- The stage advances past its old sites; its new layer starts at the resulting ordinal. -/
private theorem advance_nodes (K : ℕ) (c : Cursor) (s : Stage) :
    (allocate K c s).next.node=c.node+s.nodes := by cases s <;> rfl

private theorem stage_node_space (s : Stage) : s.nodes+successors s≤ s.heapWords := by
  cases s with
  | shrink x =>
    change x.originalSites+x.outputSites ≤ 15*x.motifs+8*x.oldEdges+2*x.oldBase+7*x.newEdges+
      x.newEdges*x.residual+2+(7+6*x.localCapacity+8*x.newDegree)*x.outputSites+2*x.originalSites
    have h : x.outputSites≤(7+6*x.localCapacity+8*x.newDegree)*x.outputSites :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  | refresh v m l h p =>
    let n := RefreshStageLayout.counts v m l h p
    change n.nodes+n.nodes ≤ n.choiceSpan+n.sparseSpan+n.splitSpan+n.graphSpan+n.newWidthSpan+
      (15+8*(1+h+p))*n.nodes
    have cap : 2*n.nodes≤(15+8*(1+h+p))*n.nodes := Nat.mul_le_mul_right _ (by omega)
    omega

private theorem successor_sum (ss : List Stage) :
    (ss.map successors).sum ≤ (ss.map Stage.heapWords).sum := by
  induction ss with
  | nil => exact le_rfl
  | cons s ss ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add ((Nat.le_add_left _ _).trans (stage_node_space s)) ih

private theorem layer_counts (K : ℕ) (ss : List Stage) (c : Cursor) (l : Layer) :
    ((nodeLayers K ss c l).map (fun row=>row.actual.count)).sum =
      l.count+(ss.map successors).sum := by
  induction ss generalizing c l with
  | nil => simp [nodeLayers]
  | cons s ss ih => simp [nodeLayers,ih,nodeLayer]

private theorem all_node_ends (K bound : ℕ) (ss : List Stage) (c : Cursor) (l : Layer)
    (start : l.first+l.count≤bound) (heap : c.node+(ss.map Stage.heapWords).sum≤bound) :
    (∀ row∈nodeLayers K ss c l,row.actual.first+row.actual.count≤bound) ∧
      (lastLayer K ss c l).first+(lastLayer K ss c l).count≤bound := by
  induction ss generalizing c l with
  | nil =>
    refine ⟨?_,start⟩
    intro row member
    have eq : row=⟨l,⟨true,0,0⟩⟩ := List.mem_singleton.mp member
    rw [eq]
    exact start
  | cons s ss ih =>
    simp only [List.map_cons,List.sum_cons] at heap
    have pay := stage_node_space s
    have nextStart : (nodeLayer K c s).first+(nodeLayer K c s).count≤bound := by
      change (allocate K c s).next.node+successors s≤bound
      rw [advance_nodes]
      omega
    have nextHeap : (allocate K c s).next.node+(ss.map Stage.heapWords).sum≤bound := by
      rw [advance_nodes]
      omega
    obtain ⟨rest,last⟩ := ih (allocate K c s).next (nodeLayer K c s) nextStart nextHeap
    refine ⟨?_,last⟩
    intro row member
    rcases List.mem_cons.mp member with rfl | mem
    · exact start
    · exact rest _ mem

private theorem initial_nodes {F : Type} [Field F] {s : ℕ} (P : Program F s) (rem v : ℕ)
    {hd : Stage} {tail : List Stage} (h : P.directory rem v=hd::tail) :
    hd.nodes=v*2^(P.charge+rem) := by
  cases P with
  | done => simp [Program.directory] at h
  | shrink s t T small p =>
    rw [←(List.cons.inj h).1]
    simpa only [Stage.nodes,Program.charge,Nat.add_assoc] using
      (Program.shrink_positions s t (p.charge+rem) v).1
  | refresh s t height pad c γ C T hm hh sym rows zero conn deg p =>
    rw [←(List.cons.inj h).1]
    simpa only [Stage.nodes,Program.charge,Nat.add_assoc] using
      (Program.refresh_positions s (p.charge+rem) v height pad).1

private theorem last_first_mono (K : ℕ) (ss : List Stage) (c : Cursor) (l : Layer)
    (same : l.first=c.node) : c.node≤(lastLayer K ss c l).first := by
  induction ss generalizing c l with
  | nil => exact same.ge
  | cons s ss ih =>
    have next := ih (allocate K c s).next (nodeLayer K c s) rfl
    have step := advance_nodes K c s
    change c.node≤(lastLayer K ss (allocate K c s).next (nodeLayer K c s)).first
    omega

/-- All cursor-zero lanes occur in the node archive. When a first stage is
present, its input nodes precede its output and every later layer. -/
theorem program_lanes_le_final {F : Type} [Field F] {s : ℕ} (P : Program F s)
    (p : Parameters) (rem degree W : ℕ) (axes : p.axes=P.charge+rem) (pos : 0<p.axes) :
    let A:=p.archive degree W
    let ss:=P.directory rem p.axes
    let R:=p.rootArchive A (p.nodeArchive A ss W) ss W
    R.initialLanes≤R.firstFinal+R.rootCount := by
  intro A ss R
  change 2^p.axes≤(lastLayer A.K ss A.cursor A.seedLayer).first+
    (lastLayer A.K ss A.cursor A.seedLayer).count
  have seed : 2^p.axes≤p.axes*2^p.axes := Nat.le_mul_of_pos_left _ pos
  cases eq : ss with
  | nil =>
    change 2^p.axes≤0+p.axes*2^p.axes
    omega
  | cons hd tl =>
    have head : hd.nodes=p.axes*2^p.axes := by
      rw [initial_nodes P rem p.axes eq,←axes]
    have start := last_first_mono A.K tl (allocate A.K A.cursor hd).next (nodeLayer A.K A.cursor hd) rfl
    have shift := advance_nodes A.K A.cursor hd
    simp only [lastLayer]
    omega

/-- The two node banks have room for every published layer and for the terminal roots.
The seed contributes the old sites of the first stage. New layers contribute the output
sites of their preceding stage, including the final layer with an identity parent. -/
theorem node_count_space {F : Type} [Field F] (B : Block F) (p : Parameters) {u rem low : ℕ}
    (hu : 40≤u) (levels : B.levels+1≤u) (factor : B.allocations.sum≤u)
    (half : low=u^10/2) (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (axes : p.axes=(B.repeat (u^8)).charge+rem) :
    let k := (B.repeat (u^8)).charge+rem
    let ss := (B.repeat (u^8)).directory rem k
    let A := p.archive (2^(B.exponent 0)) (16*u^10)
    let rows := nodeLayers A.K ss A.cursor A.seedLayer
    let last := lastLayer A.K ss A.cursor A.seedLayer
    (∀ row∈rows,8*(row.actual.first+row.actual.count)≤2^(u^10-u^4)) ∧
      8*(last.first+last.count)≤2^(u^10-u^4) ∧
      8*(rows.map (fun row=>row.actual.count)).sum≤2^(u^10-u^4) := by
  intro k ss A rows last
  let limit := (ss.map Stage.heapWords).sum
  have budget : 8*limit≤2^(u^10-u^4) := B.cursor_heap_space hu levels factor half depth
  have nonempty : ss≠[] := by
    intro empty
    have eq := Program.directory_length (B.repeat (u^8)) rem k
    change ss.length=(B.repeat (u^8)).length at eq
    rw [empty,program_length,B.repeat_effects_length] at eq
    have pos : 0<(B.levels+1)*u^8 := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    simp only [List.length_nil] at eq
    omega
  have used : k*2^k+(ss.map successors).sum≤limit := by
    cases eq : ss with
    | nil => exact (nonempty eq).elim
    | cons hd tail =>
      have head : hd.nodes=k*2^k := initial_nodes (B.repeat (u^8)) rem k eq
      have pay := stage_node_space hd
      have rest := successor_sum tail
      simp only [limit,eq,List.map_cons,List.sum_cons]
      omega
  have start : A.seedLayer.first+A.seedLayer.count≤limit := by
    change 0+p.axes*2^p.axes≤limit
    rw [show p.axes=k from axes]
    omega
  have ⟨all,final⟩ := all_node_ends A.K limit ss A.cursor A.seedLayer start
    (by change 0+limit≤limit; omega)
  refine ⟨fun row mem=>(Nat.mul_le_mul_left 8 (all row mem)).trans budget,
    (Nat.mul_le_mul_left 8 final).trans budget,?_⟩
  refine (Nat.mul_le_mul_left 8 ?_).trans budget
  change ((nodeLayers A.K ss A.cursor A.seedLayer).map (fun row=>row.actual.count)).sum≤limit
  rw [layer_counts]
  change p.axes*2^p.axes+(ss.map successors).sum≤limit
  simpa only [show p.axes=k from axes] using used


end
end ThreeFlat.Diagonal.NavigationPass

end OAI
