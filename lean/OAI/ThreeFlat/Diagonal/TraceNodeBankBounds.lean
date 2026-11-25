import OAI.ThreeFlat.Diagonal.TraceArchiveExtent
import OAI.ThreeFlat.Diagonal.TraceNodeBankLayout
import OAI.ThreeFlat.Diagonal.TraceNodeHeaderMount
import OAI.ThreeFlat.Diagonal.TraceNodeJournalSource

namespace OAI
/-! # Bounds for the actual chronological trace-node bank -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows NavigationDirectory PhysicalStage TraceNodeHeaders
open scoped Classical
noncomputable section

/-- Every source pointer in the node header comes from an actual natural word of the
executed stage journal, including pointers to arrays of length zero. -/
theorem pointer_fields {W K : ℕ} (ops : List Stage) (c : Cursor) (s : Layer) (m : Memory W)
    (mounted : MountedAt (natural m) K ops c) (sk : s.kind<2^W) (sc : s.children<2^W)
    (ske : s.kernels<2^W) (si : s.incident<2^W) (wide : 2<2^W)
    (q : Layers) (member : q∈nodeLayers K ops c s) :
    q.actual.kind<2^W ∧ q.actual.children<2^W ∧ q.actual.kernels<2^W ∧ q.actual.incident<2^W ∧
      q.parent.owners<2^W ∧ q.parent.first≤c.node+(ops.map Stage.nodes).sum := by
  induction ops generalizing c s with
  | nil =>
    obtain rfl := List.mem_singleton.mp member
    exact ⟨sk,sc,ske,si,Nat.two_pow_pos W,Nat.zero_le _⟩
  | cons op tail ih =>
    have head (x : ℕ) (bound : x<64) (used : x≠27) : (allocate K c op).words x<2^W :=
      by rw [←mounted.1 x bound used]; exact (m (c.header+x)).isLt
    have next : (allocate K c op).next.node=c.node+op.nodes := by cases op <;> rfl
    rcases List.mem_cons.mp member with rfl|rest
    · refine ⟨sk,sc,ske,si,head 44 (by decide) (by decide),?_⟩
      simp only [next,List.map_cons,List.sum_cons]
      omega
    · have kind : (nodeLayer K c op).kind<2^W := by
        cases op with
        | shrink => exact (by omega : 1<2^W)
        | refresh => exact wide
      obtain ⟨a,b,d,e,f,g⟩ := ih _ _ mounted.2 kind (head 42 (by decide) (by decide))
        (head 34 (by decide) (by decide)) (head 38 (by decide) (by decide)) rest
      exact ⟨a,b,d,e,f,g.trans_eq (by simp only [next,List.map_cons,List.sum_cons,Nat.add_assoc])⟩

theorem actual_positive (K : ℕ) (ops : List Stage) (c : Cursor) (s : Layer) (start : 0<s.count)
    (live : ∀op∈ops,0<successors op) (q : Layers) (mem : q∈nodeLayers K ops c s) :
    0<q.actual.count := by
  induction ops generalizing c s with
  | nil => obtain rfl := List.mem_singleton.mp mem;exact start
  | cons op ops ih =>
    rcases List.mem_cons.mp mem with rfl|tail
    · exact start
    · exact ih _ _ (live _ (by simp)) (fun o ho=>live o (by simp [ho])) tail

theorem actual_arity (K : ℕ) (ops : List Stage) (c : Cursor) (s : Layer) (cc : ℕ)
    (start : s.childCount≤cc) (f : ∀op∈ops,childArity op≤cc)
    (q : Layers) (mem : q∈nodeLayers K ops c s) : q.actual.childCount≤cc := by
  induction ops generalizing c s with
  | nil => obtain rfl := List.mem_singleton.mp mem;exact start
  | cons op ops ih =>
    rcases List.mem_cons.mp mem with rfl|tail
    · exact start
    · exact ih _ _ (f _ (by simp)) (fun o ho=>f o (by simp [ho])) tail

/-- Physical loop budget at a literal upper bound on the size of one layer. -/
def rowBudget (W : ℕ) (a : NodeArchive) (limit : ℕ) :=
  ticks W a.banks a.childCap a.halfCap a.motifCap limit

theorem ticks_mono (W : ℕ) (a : NodeArchive) {n limit : ℕ} (h : n≤limit) :
    ticks W a.banks a.childCap a.halfCap a.motifCap n≤rowBudget W a limit := by
  dsimp only [rowBudget,ticks]
  gcongr

/-- The same four physical range proofs and the same numerical budget are used by
the header builder, the stage writer, the final registration and the preserved-memory frame. -/
theorem bank_bounds_at {W ctrl headerBase charges nodes limit unit K lanes perLane pairs trace tariff cc hc mc : ℕ}
    (space : BankSpace W ctrl headerBase charges nodes limit unit)
    (ops : List Stage) (c : Cursor) (s : Layer) (m : Memory W) (xs : List NodeRow) (last : Layer)
    (H M : ℕ) (seen : TraceRecovery.stagePost K ops c s (·<ctrl) (natural m) H M
      (fun _=>False) xs last)
    (mounted : MountedAt (natural m) K ops c)
    (compact : 16*(ops.length+1)≤unit)
    (source : c.header+64*ops.length+44≤ctrl)
    (occupancy : 8*(c.node+s.count+(ops.map Stage.heapWords).sum)≤unit)
    (first : s.first=c.node) (positive : 0<s.count) (live : ∀op∈ops,0<successors op)
    (sk : s.kind<2^W) (sc : s.children<2^W) (ske : s.kernels<2^W) (si : s.incident<2^W)
    (arity : s.childCount≤cc) (gates : ∀op∈ops,childArity op≤cc)
    (caps : max cc (max hc mc)<2^W) (lane : lanes<2^W) (per : perLane<2^W)
    (pair : pairs<2^W) (laneSpan : lanes*perLane≤2^W)
    (bound : ℕ) (perRow : ∀ q∈nodeLayers K ops c s,q.actual.count≤bound) :
    let a := spacedArchive ctrl headerBase charges nodes lanes perLane pairs trace tariff cc hc mc
    let rows := NodePublication.records xs
    RunBounds W a rows (rowBudget W a bound) ∧ TapeBounds W a rows ∧
      ScanRoom W ctrl (ctrl+1) c.header a.headerBase ops.length ∧
      BankInterval a rows ctrl limit ∧
      ∀ i : Fin rows.length,a.banks.charges+2*((rows.get i).actual.first+(rows.get i).actual.count)≤limit := by
  intro a rows
  obtain ⟨minUnit,controls,headerRoom,chargeRoom,nodeRoom,top⟩ := space
  have eqRows : rows=nodeLayers K ops c s := seen.1
  have len : rows.length=ops.length+1 := by rw [eqRows,nodeLayers_length]
  have actual (i : Fin rows.length) : rows.get i∈nodeLayers K ops c s := by
    rw [←eqRows]
    exact List.get_mem rows i
  have span (i : Fin rows.length) := actual_span K ops c s first _ (actual i)
  have head (i : Fin rows.length) : hdr a i.val+16≤a.banks.charges := by
    change headerBase+16*i.val+16≤charges
    have cut := i.isLt
    omega
  have charge (i : Fin rows.length) : a.banks.charges+2*((rows.get i).actual.first+(rows.get i).actual.count)≤a.banks.nodes := by
    change charges+2*((rows.get i).actual.first+(rows.get i).actual.count)≤nodes
    have := span i
    omega
  have lastNode (i : Fin rows.length) : a.banks.nodes+8*((rows.get i).actual.first+(rows.get i).actual.count)≤limit := by
    change nodes+8*((rows.get i).actual.first+(rows.get i).actual.count)≤limit
    have := span i
    omega
  have owner (i : Fin rows.length) (active : (rows.get i).parent.finalLayer=false) :
      (rows.get i).parent.owners+(rows.get i).actual.count≤ctrl := by
    have entry : ∃ q∈xs, (⟨q.layer,q.parent⟩:Layers)=rows.get i := List.mem_map.mp (List.get_mem rows i)
    obtain ⟨q,hq,eq⟩ := entry
    have nz := actual_positive K ops c s positive live _ (actual i)
    rw [←eq] at nz active ⊢
    let k : Fin q.layer.count := ⟨q.layer.count-1,by change 0<q.layer.count at nz;omega⟩
    have held := (seen.2.2 q hq).ownerCells active k
    change q.parent.owners+(q.layer.count-1)<ctrl at held
    change 0<q.layer.count at nz
    change q.parent.owners+q.layer.count≤_
    omega
  have bankHead : a.headerBase+16*rows.length≤a.banks.charges := by
    change headerBase+16*rows.length≤charges
    omega
  have wide : 16<2^W := by omega
  have clock : RunBounds W a rows (rowBudget W a bound) := by
    refine ⟨?_,?_,?_,?_,?_,?_,fun i=>ticks_mono _ _ (perRow _ (actual i))⟩
    · change ctrl+15<charges;omega
    · change ctrl+15≠ctrl+14;omega
    · change ctrl+15<_;omega
    · change ctrl+14<_;omega
    · omega
    · intro i
      refine ⟨wide,?_,head i,charge i,(lastNode i).trans_lt top,?_,
        actual_arity K ops c s cc arity gates _ (actual i),caps,lane,pair,per,?_⟩
      · change ctrl+14<charges;omega
      · intro nonfinal
        exact (owner i nonfinal).trans (by change ctrl≤charges;omega)
      · intro v _ lt
        by_cases empty : perLane=0
        · change v.val*perLane<_;rw [empty,Nat.mul_zero];omega
        · change v.val<lanes at lt
          change v.val*perLane<2^W
          exact (Nat.mul_lt_mul_of_pos_right lt (Nat.pos_of_ne_zero empty)).trans_le laneSpan
  have tape : TapeBounds W a rows := by
    refine ⟨?_,?_,bankHead,?_⟩
    · change ctrl+14<headerBase;omega
    · change ctrl+15<headerBase;omega
    · intro i col
      obtain ⟨kd,ch,ke,inc,own,par⟩ := pointer_fields ops c s m mounted sk sc ske si (by omega) _ (actual i)
      have cap := actual_arity K ops c s cc arity gates _ (actual i)
      have qs := span i
      have cost := charge i
      have tail := lastNode i
      have iu := i.isLt
      change charges+2*((rows.get i).actual.first+(rows.get i).actual.count)≤nodes at cost
      change nodes+8*((rows.get i).actual.first+(rows.get i).actual.count)≤limit at tail
      have full : cc<2^W := (le_max_left ..).trans_lt caps
      have prior := node_counts_heap ops
      fin_cases col <;> simp only [header,hdr] <;>
        first | exact kd | exact ch | exact ke | exact inc | exact own | split <;> omega |
          (change headerBase+16*(i.val+1)<_;omega) |
          (change charges+2*(rows.get i).actual.first<_;omega) |
          (change nodes+8*(rows.get i).actual.first<_;omega) | omega
  have frame : BankInterval a rows ctrl limit := by
    refine ⟨?_,?_,?_,?_,?_,?_,lastNode⟩
    · change ctrl≤ctrl+15 ∧ ctrl+15<limit;omega
    · change ctrl≤ctrl+14 ∧ ctrl+14<limit;omega
    · change ctrl≤headerBase ∧ headerBase+16*rows.length≤limit;omega
    · change ctrl≤charges;omega
    · change ctrl≤nodes;omega
    · intro i;exact (charge i).trans (by change nodes≤limit;omega)
  refine ⟨clock,tape,?_,frame,frame.chargeEnd⟩
  constructor
  · change ctrl<headerBase;omega
  · change ctrl+1+12<headerBase;omega
  · change c.header+64*ops.length≤headerBase;omega
  · exact source.trans_lt (by omega)
  · change headerBase+16*(ops.length+1)<_
    omega

/-- The same four physical range proofs and the same numerical budget are used by
the header builder, the stage writer, the final registration and the preserved-memory frame. -/
theorem bank_bounds {w K lanes perLane pairs trace tariff cc hc mc : ℕ} (hw : 1≤w)
    (ops : List Stage) (c : Cursor) (s : Layer) (m : Memory (64*w)) (xs : List NodeRow) (last : Layer)
    (H M : ℕ) (seen : TraceRecovery.stagePost K ops c s (·<compactControl w) (natural m) H M
      (fun _=>False) xs last)
    (mounted : MountedAt (natural m) K ops c)
    (compact : 16*(ops.length+1)≤traceUnit w)
    (source : c.header+64*ops.length+44≤compactControl w)
    (occupancy : 8*(c.node+s.count+(ops.map Stage.heapWords).sum)≤traceUnit w)
    (first : s.first=c.node) (positive : 0<s.count) (live : ∀op∈ops,0<successors op)
    (sk : s.kind<2^(64*w)) (sc : s.children<2^(64*w)) (ske : s.kernels<2^(64*w)) (si : s.incident<2^(64*w))
    (arity : s.childCount≤cc) (gates : ∀op∈ops,childArity op≤cc)
    (caps : max cc (max hc mc)<2^(64*w)) (lane : lanes<2^(64*w)) (per : perLane<2^(64*w))
    (pair : pairs<2^(64*w)) (laneSpan : lanes*perLane≤2^(64*w))
    (bound : ℕ) (perRow : ∀ q∈nodeLayers K ops c s,q.actual.count≤bound) :
    let a := traceArchive w lanes perLane pairs trace tariff cc hc mc
    let rows := NodePublication.records xs
    RunBounds (64*w) a rows (rowBudget (64*w) a bound) ∧ TapeBounds (64*w) a rows ∧
      ScanRoom (64*w) (compactControl w) (compactHead w) c.header a.headerBase ops.length ∧
      BankInterval a rows (compactControl w) (traceLimit w) ∧
      ∀ i : Fin rows.length,a.banks.charges+2*((rows.get i).actual.first+(rows.get i).actual.count)≤traceLimit w := by
  obtain ⟨unit,large,top⟩ := trace_sector hw
  have space : BankSpace (64*w) (compactControl w) (traceBase w+8*traceUnit w)
      (traceBase w+12*traceUnit w) (traceBase w+16*traceUnit w) (traceLimit w) (traceUnit w) := by
    constructor <;> try unfold compactControl
    all_goals omega
  exact bank_bounds_at (trace:=trace) (tariff:=tariff) space ops c s m xs last H M seen mounted
    compact source occupancy first positive live sk sc ske si arity gates caps lane per pair laneSpan bound perRow

end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
