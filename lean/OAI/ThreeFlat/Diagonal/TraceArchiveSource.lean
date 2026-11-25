import OAI.ThreeFlat.Diagonal.PhysicalArchiveRowFields
import OAI.ThreeFlat.Diagonal.NavigationArchiveFields
import OAI.ThreeFlat.RAM.NavigationNodeRows

namespace OAI
/-! # Mounted row contents and structural extent of an executed stage directory -/

namespace ThreeFlat.Diagonal.NavigationPass.TraceRecovery
open PhysicalStage NavigationDirectory RAM RAM.NavigationNodeRows
open scoped Classical
noncomputable section

structure RowContents {s : Layer} (d : LayerData s) («protected» : ℕ→Prop) (mem : ℕ→ℕ)
    (halfCap motifCap : ℕ) : Prop where
  reads : d.Reads mem
  footprint : d.Footprint «protected» mem
  halves : ∀ j,(d.halfWidth j).length≤halfCap
  motifs : s.kind≠0 → ∀ j,(d.motifCopies j).length≤motifCap

structure ArchivedSource (row : NodeRow) («protected» : ℕ→Prop) (mem : ℕ→ℕ) (halfCap motifCap : ℕ) (initial : Layer→Prop) : Prop where
  contents : initial row.layer ∨ RowContents row.data «protected» mem halfCap motifCap
  parents : ParentReads row.parent row.owners mem
  ownerCells : row.parent.finalLayer=false → ∀ j : Fin row.layer.count,«protected» (row.parent.owners+j.val)

def lastLayer (K : ℕ) : List Stage → Cursor → Layer → Layer
  | [],_,a => a
  | s::ss,c,_ => lastLayer K ss (allocate K c s).next (nodeLayer K c s)

def records (xs : List NodeRow) : List Layers := xs.map fun q=>⟨q.layer,q.parent⟩

def stagePost (K : ℕ) (ops : List Stage) (c : Cursor) (s : Layer)
    («protected» : ℕ→Prop) (mem : ℕ→ℕ) (H M : ℕ) (initial : Layer→Prop) (xs : List NodeRow) (last : Layer) : Prop :=
  records xs=nodeLayers K ops c s ∧ last=lastLayer K ops c s ∧
    ∀ q∈xs, ArchivedSource q «protected» mem H M initial

theorem lastLayer_mem (K : ℕ) (ops : List Stage) (c : Cursor) (s : Layer) :
    ∃ q ∈ nodeLayers K ops c s, q.actual = lastLayer K ops c s := by
  induction ops generalizing c s with
  | nil => exact ⟨_,List.mem_cons_self,rfl⟩
  | cons step rest ih =>
    obtain ⟨q,inside,same⟩ := ih (allocate K c step).next (nodeLayer K c step)
    exact ⟨q,List.mem_cons_of_mem _ inside,same⟩

theorem stagePost.last_mem {K ops c s «protected» m H M initial xs last}
    (h : stagePost K ops c s «protected» m H M initial xs last) :
    ∃ q ∈ nodeLayers K ops c s, q.actual = last := by
  rw [h.2.1]
  exact lastLayer_mem K ops c s

/-- Subsequent node publication and registration preserve the recovered source
archive as soon as they preserve its occupied words, regardless of all newer banks. -/
theorem stagePost.transfer {K H M : ℕ} {ops : List Stage} {c : Cursor} {s last : Layer}
    {«protected» «protected'» : ℕ→Prop} {mem mem' : ℕ→ℕ} {xs : List NodeRow} {initial : Layer→Prop}
    (post : stagePost K ops c s «protected» mem H M initial xs last)
    (same : ∀ i, «protected» i → mem' i=mem i) (widen : ∀ i, «protected» i → «protected'» i) :
    stagePost K ops c s «protected'» mem' H M initial xs last := by
  refine ⟨post.1,post.2.1,?_⟩
  intro q hit
  let row := post.2.2 q hit
  refine ⟨row.contents.imp_right (fun src => ⟨src.reads.of_footprint src.footprint same,
    (src.footprint.transfer src.footprint same).mono widen,src.halves,src.motifs⟩),?_,?_⟩
  · intro nh j
    exact (same _ (row.ownerCells nh j)).trans (row.parents nh j)
  · intro nh j
    exact widen _ (row.ownerCells nh j)

/-- All node identifiers are bounded by finite directory word counts before any
histogram is decoded. Neither the branch chosen nor its owner maps enter this bound. -/
theorem node_room (K : ℕ) (ops : List Stage) (c : Cursor) (layer : Layer) (first : layer.first=c.node)
    (q : Layers) (hit : q ∈ nodeLayers K ops c layer) :
    q.actual.first+q.actual.count ≤ c.node+layer.count+(ops.map Stage.nodes).sum+(ops.map successors).sum := by
  induction ops generalizing c layer with
  | nil =>
    obtain rfl := List.mem_singleton.mp hit
    simp [first]
  | cons op rest ih =>
    obtain eq | tail := List.mem_cons.mp hit
    · subst q
      simp [first]
      omega
    · have bound := ih (allocate K c op).next (nodeLayer K c op) rfl tail
      have next : (allocate K c op).next.node=c.node+op.nodes := by cases op <;> rfl
      change _ ≤ (allocate K c op).next.node+successors op+_+_ at bound
      rw [next] at bound
      simp only [List.map_cons,List.sum_cons]
      omega

end
end ThreeFlat.Diagonal.NavigationPass.TraceRecovery

end OAI
