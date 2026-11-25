import OAI.ThreeFlat.Diagonal.CompressorNodeDimensions
import OAI.ThreeFlat.Diagonal.RefreshStageLayout

namespace OAI
/-! # Static address allocation for the chronological compressor sweeps

Each header has 64 words, including the long shrinking header. All histogram counts use one
contiguous dense area. Every new adjacency/width array is retained for the selected-site
compiler and is the actual input to the next stage. Widths never enter address allocation.
-/

namespace ThreeFlat.Diagonal.NavigationDirectory

open CompressorPacking.Native.ShrinkStage

inductive Stage where
  | shrink (x : Dimensions)
  | refresh (base ports lanes h pad : ℕ)

structure Cursor where
  header : ℕ
  dense : ℕ
  heap : ℕ
  node : ℕ
  graph : ℕ
  width : ℕ
  deriving DecidableEq

structure Entry where
  words : ℕ → ℕ
  next : Cursor

def Stage.motifs : Stage → ℕ
  | .shrink x => x.motifs
  | .refresh v m l h p => (RefreshStageLayout.counts v m l h p).motifs

def Stage.nodes : Stage → ℕ
  | .shrink x => x.originalSites
  | .refresh v m l h p => (RefreshStageLayout.counts v m l h p).nodes

def allocate (K : ℕ) (c : Cursor) : Stage → Entry
  | .shrink x =>
    let choice := c.heap
    let supply := choice+3*x.motifs
    let demand := supply+8*x.motifs
    let split := demand+2*x.motifs
    let colors := split+8*x.oldEdges
    let offsets := colors+x.oldBase
    let graph := offsets+x.oldBase
    let keys := graph+6*x.newEdges
    let width := keys+x.newEdges
    let costs := width+x.newEdges*x.residual
    let heap := costs+2*(x.motifs+1)
    let next := c.header+64
    let p : Pointers := ⟨c.dense,choice,supply,next,c.node,demand,c.graph,c.width,split,colors,offsets,
      graph,keys,width,costs,c.header⟩
    ⟨(fun i => if i<34 then headerWord x p i else if i=48 then x.oldDegree else headerExtra x heap i),
      ⟨next,c.dense+K*x.motifs,extraEnd x heap,c.node+x.originalSites,graph,width⟩⟩
  | .refresh v m l h pad =>
    let x := RefreshStageLayout.counts v m l h pad
    let choice := c.heap
    let supply := choice+x.choiceSpan
    let split := supply+x.sparseSpan
    let graph := split+x.splitSpan
    let width := graph+x.graphSpan
    let next := c.header+64
    let p : RefreshStageLayout.Pointers := ⟨c.dense,choice,supply,next,c.node,c.width,c.graph,
      split,graph,width⟩
    let extra := width+x.newWidthSpan
    ⟨(fun i => if i<34 then RefreshStageLayout.words v m l h pad p i else if i=48 then m else
        RefreshStageLayout.headerExtra x (1+h+pad) extra i),
      ⟨next,c.dense+K*x.motifs,RefreshStageLayout.extraEnd x (1+h+pad) extra,c.node+x.nodes,graph,width⟩⟩

/-- One rectangular public tape, in increasing chronological-header order. -/
def tape (K : ℕ) : List Stage → Cursor → List ℕ
  | [], _ => []
  | s::ss, c => List.ofFn (fun i : Fin 64 => (allocate K c s).words i.val) ++
    tape K ss (allocate K c s).next

def finish (K : ℕ) : List Stage → Cursor → Cursor
  | [], c => c
  | s::ss, c => finish K ss (allocate K c s).next

/-- Number of persistent words reserved by one stage. All bounds are independent of
the unknown histogram values and of the absolute initial heap address. -/
def Stage.heapWords : Stage → ℕ
  | .shrink x => 15*x.motifs+8*x.oldEdges+2*x.oldBase+7*x.newEdges+x.newEdges*x.residual+
      2+(7+6*x.localCapacity+8*x.newDegree)*x.outputSites+2*x.originalSites
  | .refresh v m l h pad =>
      let n := RefreshStageLayout.counts v m l h pad
      n.choiceSpan+n.sparseSpan+n.splitSpan+n.graphSpan+n.newWidthSpan+
        (15+8*(1+h+pad))*n.nodes

theorem heap_step (K : ℕ) (c : Cursor) (s : Stage) :
    (allocate K c s).next.heap = c.heap+s.heapWords := by
  cases s with
  | shrink x =>
    simp only [allocate,CompressorPacking.Native.ShrinkStage.extra_extent,Stage.heapWords]
    ring
  | refresh v m l h pad =>
    simp only [allocate,RefreshStageLayout.extra_extent,Stage.heapWords]
    ring

theorem heap_finish (K : ℕ) (ss : List Stage) (c : Cursor) :
    (finish K ss c).heap=c.heap+(ss.map Stage.heapWords).sum := by
  induction ss generalizing c with
  | nil => simp [finish]
  | cons s ss ih => rw [finish,ih,heap_step]; simp [Nat.add_assoc]

theorem header_finish (K : ℕ) (ss : List Stage) (c : Cursor) :
    (finish K ss c).header=c.header+64*ss.length := by
  induction ss generalizing c with
  | nil => simp [finish]
  | cons s ss ih =>
    have one : (allocate K c s).next.header=c.header+64 := by cases s <;> rfl
    rw [finish,ih,one]
    simp [Nat.mul_add,Nat.add_assoc,Nat.add_comm]

theorem finish_append (K : ℕ) (a b : List Stage) (c : Cursor) :
    finish K (a++b) c=finish K b (finish K a c) := by
  induction a generalizing c with
  | nil => rfl
  | cons a as ih => exact ih _

theorem tape_append (K : ℕ) (a b : List Stage) (c : Cursor) :
    tape K (a++b) c=tape K a c++tape K b (finish K a c) := by
  induction a generalizing c with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append,tape,finish,ih,List.append_assoc]

@[simp] theorem tape_length (K : ℕ) (ss : List Stage) (c : Cursor) : (tape K ss c).length=64*ss.length := by
  induction ss generalizing c with
  | nil => rfl
  | cons s ss ih =>
    rw [tape,List.length_append,List.length_ofFn,ih,List.length_cons,Nat.mul_succ,Nat.add_comm]

/-- The live stage reads the entire real 64-word header from the physical static tape. -/
theorem tape_header (K : ℕ) (pre : List Stage) (s : Stage) (post : List Stage) (c : Cursor)
    (i : Fin 64) :
    ((tape K (pre++s::post) c)[64*pre.length+i.val]?) =
      some ((allocate K (finish K pre c) s).words i.val) := by
  have skip : (tape K pre c).length ≤ 64*pre.length+i.val := by rw [tape_length]; omega
  rw [tape_append,List.getElem?_append_right skip,tape_length,Nat.add_sub_cancel_left,tape,
    List.getElem?_append_left (by rw [List.length_ofFn]; exact i.isLt)]
  simp only [List.getElem?_ofFn,dite_eq_left i.isLt]

theorem shrink_heap_le (x : Dimensions) (hd : 0<x.oldDegree) (hj : 0<x.tagRadix)
    (hr : 0<x.residual) (out : x.outputSites≤x.originalSites) :
    (Stage.shrink x).heapWords≤2+
      (22*(8*x.oldDegree+6*x.newDegree+6)+(7+6*x.localCapacity+8*x.newDegree)+2)*x.originalSites := by
  let q := x.originalSites*(8*x.oldDegree+6*x.newDegree+6)
  have spans : ∀ n∈x.preLengths++x.postLengths,n≤q := span_extent x hd hj hr
  have e1 := spans (8*x.oldEdges) (by simp [Dimensions.preLengths])
  have e2 := spans x.oldBase (by simp [Dimensions.preLengths])
  have e3 := spans (2*x.motifs) (by simp [Dimensions.preLengths])
  have e4 := spans (6*x.newEdges) (by simp [Dimensions.postLengths])
  have e5 := spans (x.newEdges*x.residual) (by simp [Dimensions.postLengths])
  have e6 := Nat.mul_le_mul_left (7+6*x.localCapacity+8*x.newDegree) out
  change 15*x.motifs+8*x.oldEdges+2*x.oldBase+7*x.newEdges+x.newEdges*x.residual+
    2+(7+6*x.localCapacity+8*x.newDegree)*x.outputSites+2*x.originalSites≤_
  calc
    _ ≤ 2+22*q+(7+6*x.localCapacity+8*x.newDegree)*x.originalSites+2*x.originalSites := by omega
    _ = _ := by unfold q; ring

theorem refresh_heap_le (v m l h pad : ℕ) (hm : 0 < m) (hl : 0 < l) :
    (Stage.refresh v m l h pad).heapWords≤(21+h+15*(1+h+pad))*(v*m*l) := by
  let n := RefreshStageLayout.counts v m l h pad
  let P := v*m*l
  obtain ⟨_,nodes,_,_,_,width,split,choice,graph,sparse,_⟩ :=
    RefreshStageLayout.bounded (K:=0) hm hl (show v*m*l≤P from le_rfl)
  have en := Nat.mul_le_mul_left (15+8*(1+h+pad)) nodes
  change n.choiceSpan+n.sparseSpan+n.splitSpan+n.graphSpan+n.newWidthSpan+(15+8*(1+h+pad))*n.nodes≤_
  calc
    _ ≤ 3*P+h*P+3*P+6*(1+h+pad)*P+(1+h+pad)*P+(15+8*(1+h+pad))*P :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add choice sparse) split) graph) width) en
    _ = _ := by unfold P; ring

/-- The native selected-site interpreter dispatches on the previous port degree and the
stored node kind. This coordinate is copied from the fixed finite schedule. -/
theorem family_degree (K : ℕ) (c : Cursor) (s : Stage) :
    (allocate K c s).words 48 = (match s with | .shrink x => x.oldDegree | .refresh _ m _ _ _ => m) := by
  cases s <;> rfl

theorem header_words (K : ℕ) (c : Cursor) (s : Stage) :
    (allocate K c s).words 0=s.motifs ∧ (allocate K c s).words 1=c.dense ∧
    (allocate K c s).words 4=c.header+64 ∧ (allocate K c s).words 5=s.nodes ∧
    (allocate K c s).words 6=c.node := by cases s <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem dense_finish (K : ℕ) (ss : List Stage) (c : Cursor) :
    (finish K ss c).dense=c.dense+K*(ss.map Stage.motifs).sum := by
  induction ss generalizing c with
  | nil => simp [finish]
  | cons s ss ih =>
    rw [finish,ih]
    cases s <;> simp [allocate,Stage.motifs,Nat.mul_add,Nat.add_assoc]

theorem nodes_finish (K : ℕ) (ss : List Stage) (c : Cursor) :
    (finish K ss c).node=c.node+(ss.map Stage.nodes).sum := by
  induction ss generalizing c with
  | nil => simp [finish]
  | cons s ss ih =>
    rw [finish,ih]
    cases s <;> simp [allocate,Stage.nodes,Nat.add_assoc]

/-- Numeric bounds used by both physical admission calls on the very next stage. All
previous graphs and widths survive above their own endpoints and below the new allocation. -/
theorem successor_resident (K : ℕ) (c : Cursor) (s : Stage) :
    let out := (allocate K c s).next
    let rows := match s with
      | .shrink x=>x.newEdges
      | .refresh v m l h p=>(RefreshStageLayout.counts v m l h p).newGraphRows
    let widths := match s with
      | .shrink x=>x.newEdges*x.residual
      | .refresh v m l h p=>(RefreshStageLayout.counts v m l h p).newWidthSpan
    c.heap≤out.graph ∧ c.heap≤out.width ∧ out.graph+6*rows≤out.heap ∧ out.width+widths≤out.heap := by
  cases s with
  | shrink x =>
    simp only [allocate,CompressorPacking.Native.ShrinkStage.extra_extent]
    omega
  | refresh v m l h pad =>
    simp only [allocate,RefreshStageLayout.extra_extent,RefreshStageLayout.counts]
    omega

theorem live_limits (K : ℕ) (start : Cursor) (pre : List Stage) (s : Stage) (rest : List Stage)
    (top : ℕ)
    (static : start.header+64*(pre++s::rest).length≤ start.heap)
    (raw : start.dense+K*((pre++s::rest).map Stage.motifs).sum≤ start.heap)
    (space : start.heap+((pre++s::rest).map Stage.heapWords).sum≤top) :
    let c := finish K pre start
    c.header+64≤c.heap ∧ c.dense+K*s.motifs≤c.heap ∧ (allocate K c s).next.heap≤top := by
  intro c
  have past : start.heap≤c.heap := by rw [show c.heap=start.heap+(pre.map Stage.heapWords).sum from heap_finish ..]; omega
  constructor
  · apply le_trans _ past
    change (finish K pre start).header+64≤_
    rw [header_finish]
    rw [List.length_append,List.length_cons,Nat.mul_add,Nat.mul_add] at static
    omega
  constructor
  · apply le_trans _ past
    change (finish K pre start).dense+K*s.motifs≤_
    rw [dense_finish]
    simp only [List.map_append,List.map_cons,List.sum_append,List.sum_cons,Nat.mul_add] at raw
    omega
  · rw [heap_step,show c.heap=start.heap+(pre.map Stage.heapWords).sum from heap_finish ..]
    simp only [List.map_append,List.map_cons,List.sum_append,List.sum_cons] at space
    omega

end ThreeFlat.Diagonal.NavigationDirectory

end OAI
