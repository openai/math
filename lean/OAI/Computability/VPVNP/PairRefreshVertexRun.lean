import OAI.Computability.VPVNP.PairRefreshVertexPrefix
import OAI.Computability.VPVNP.PairRefreshTraversalMapBody

/-!
# Executing a complete refresh role from the popped DFS node

The installed finite role locates the selected level, guesses the unique older
half-wire packet, and runs the resident kernel on it and the independent newer
half. The role either returns to the DFS or reaches a rejecting opcode. All
histogram additions use the fixed global ordering of refresh scalar entries.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshVertex

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords CompressorRecords.PortRefresh CompressorRecords.RefreshMapOperands
open VertexImage NodeArguments NodeArguments.ChildScan TraversalControllerInputs TraversalRoles TraversalRows
open NewSlots MotifConversion LocalHistory
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {t hist : ℕ}
  (ties : Fin t ≃ Tie (2^S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
local notation "body" => TraversalPlan.body B ties stride order
local notation "locator" => TraversalPlan.locatorBank B ties stride order

/-- The complete native refresh vertex segment at the schedule's port exponent, with the chosen
resident body and locator registers. -/
noncomputable def refreshSegment := RefreshVertexAssembly.segment S.portExponent body locator

variable {bits pcs regs g : ℕ} (loc : Fin (refreshSegment B ties stride order).count → Fin pcs)
  (dfs : Fin 9 ↪ Fin regs) (saved : Saved ↪ Fin regs)
  (reg : Fin (refreshSegment B ties stride order).privateRegs ↪ Fin regs) (done : Fin pcs)
  (M : Machine bits pcs regs 11) (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2^S.portExponent)) (degree n rowEnd : ℕ)
  (U V : IncidenceDirectory bits) (m : Memory bits) (start older listHead : ℕ)
  (old : X.network.Half (oldSite X v))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))

local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "Y" => dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh S.port_order (And.right S.degree_bounds) choice
local notation "O" => NewSlots.sites X.baseIndex (bitWordFinEquiv g)
local notation "R" => TerminalLayout.privateRegions degree n rowEnd hist
local notation "A" => LeafArena.Regions.arguments R
local notation "histBase" => LeafArena.Regions.histBase R
local notation "cap" => BlockSchedule.Templates.recordLimit B
local notation "child" => childNode X older cap (oldSite X v)
local notation "oldBits" => packed X (oldSite X v) old
local notation "childHalf" => Child.ofHalf X (oldSite X v) old
local notation "pkt" => Child.packet X older cap childHalf
local notation "E₀" => entryInput B X choice v old new
local notation "copies" => repetitions B.refresh (EntryInput.demand E₀)
local notation "ws" => groupedWidths (bitWordFinEquiv _) (splitWidths X)
local notation "perm" => oldPortMatching (splitSlots X) (bitWordFinEquiv _)
local notation "wo" => ws (v,Prod.snd v)
local notation "wi" => ws (Equiv.symm perm (v,Prod.snd v))
local notation "bodyLoc" => RefreshVertexAssembly.bodyPC S.portExponent body locator loc
local notation "bodyBank" => RefreshVertexAssembly.bodyRegs S.portExponent body locator reg
local notation "K₀" => TraversalPlan.budget B ties stride order

set_option maxHeartbeats 1200000 in
/-- The actual branch path and private updates of a refresh vertex. The fixed
cost includes one header scan and one input packet before the motif. -/
theorem run {header first pitch offset base : ℕ} {initial : TaggedLayer} {ls : List (Fiber bits)}
    (installed : ∀ i, M.code (loc i) = ((refreshSegment B ties stride order).row loc dfs saved reg done i).resize bits)
    (apartD : ∀ i j, reg i ≠ dfs j) (apartS : ∀ i j, reg i ≠ saved j)
    (heads : Resident M.publicData m header first pitch offset cap base initial ls)
    (j : Fin (initial :: ls.map Prod.fst).length) (level : ℕ) (hj : j.val = level+1)
    (id : Fin (initial :: ls.map Prod.fst)[j].layer.count) (selected : id.val = (O v).val)
    (c : Config bits pcs regs) (entry : c.pc = loc (refreshSegment B ties stride order).entry)
    (node : (c.reg (dfs 7)).val = address cap (layerBase cap base (initial :: ls.map Prod.fst) j) id)
    (fitRows : layerBase cap base (initial :: ls.map Prod.fst) (ls.length+1) < 2^bits)
    (fields : (directory S.portExponent older cap A U).Stored m (levelHead M.publicData m level+14))
    (row : DFS.Row m (c.reg (dfs 7)).val listHead [word child])
    (levelData : TraversalHeaders.Geometry (Fintype.card X.Base) g (levelHead M.publicData m level).val
      (levelHead M.publicData m (level+1)).val start A U V m)
    {fit : Fintype.card X.Base*D*2^g*D ≤ 2^bits}
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (oldCols : U.ActualColumns X m) (newCols : V.ActualColumns Y m)
    (newData : NodeFields A (c.reg (dfs 7)).val Y (promotedSites v) new c.privateMem)
    {G role : W bits} (stack : c.reg (dfs 6) = word n)
    (geometry : ResidentGeometry (DFS.scratch n c.privateMem) G role (word histBase))
    (roleAfter : histBase ≤ (G+10).val) (histAfter : histBase ≤ (G+11).val)
    (positive : 0 < child) (before : child < (c.reg (dfs 7)).val) (parentBound : (c.reg (dfs 7)).val < rowEnd)
    (oldDegree : D ≤ degree) (newDegree : 2^(S.degreeExponent 0) ≤ degree)
    (oldWidth : X.maxWireWidth ≤ n) (newWidth : (Y).maxWireWidth ≤ n)
    (copyBound : copies ≤ n) (large : MapCallWords.headCapacity D H+12 ≤ n) (five : 5 ≤ n)
    (capacity : MapWorkspace.Capacity B.refresh bits n (R).cacheBase)
    (strideFit : cap+2 < 2^bits) (lanes : 2^g < 2^bits) (wide : D < 2^bits)
    (tableWidth : MapConstants.widthThreshold B.refresh ≤ bits) :
    let labels := TraversalPlan.emitted B order X choice v old new
    let later := ls.length-(level+1)
    ∃ out es, ChildScan.Prefix M m c out oldBits es ∧ choiceBits es = oldBits ∧
      es.length ≤ 63+6*later+16*D+6*(oldBits).length+K₀*(wo+wi+copies+1) ∧
      countProbes es ≤ 15+later+3*D+K₀ ∧
      (if labels.isSome then out.pc = done else M.code out.pc = .reject) ∧
      out.persistent = c.persistent ∧ (∀ q, q ∉ Set.range reg → out.reg q = c.reg q) ∧
      (∀ q : W bits, q.val < histBase+hist+12+2*n → (∀ l : Fin hist, q ≠ word (histBase+l.val)) →
        out.privateMem q = storePackets A [pkt] c.privateMem q) ∧
      ∀ l : Fin hist, out.privateMem (word (histBase+l.val)) = c.privateMem (word (histBase+l.val)) +
        ((labels.getD []).count l : W bits) := by
  intro labels later
  let parent := (c.reg (dfs 7)).val
  have childBound := before.trans parentBound
  have oldEnd := TraversalGeometry.argument_end degree n rowEnd hist X (oldSite X v) old child childBound oldDegree oldWidth
  have newEnd := TraversalGeometry.argument_end degree n rowEnd hist Y (promotedSites v) new parent parentBound newDegree newWidth
  have hhist : histBase + hist ≤ (R).cacheBase := Nat.le_add_right ..
  have histFits := hhist.trans_lt capacity.room
  have childFit : (A).base child+(oldBits).length < 2^bits := oldEnd.trans_lt ((Nat.le_add_right ..).trans_lt histFits)
  have parentFit := newEnd.trans ((Nat.le_add_right ..).trans histFits.le)
  have strideBound : (oldBits).length ≤ (A).stride :=
    (packed_length_le X (oldSite X v) old).trans ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 oldDegree) oldWidth).trans (Nat.le_succ _))
  have early : n < (A).base child := by
    change n < n+child*(2*degree*n+1)
    exact Nat.lt_add_of_pos_right (Nat.mul_pos positive (Nat.succ_pos _))
  obtain ⟨mid,front,atBody,located,mem,per,regs'⟩ := RefreshVertexAssembly.load_child S.portExponent body locator loc dfs saved
    reg done M installed X (oldSite X v) old U m A older cap listHead heads j level hj id c entry node fitRows fields row
    oldCols strideFit (before.trans (c.reg (dfs 7)).isLt) childFit
  have geom' := RefreshVertexPacket.geometry X (oldSite X v) old A older cap c.privateMem G role (word histBase)
    geometry early (oldEnd.trans roleAfter) (oldEnd.trans histAfter)
  have old' := RefreshVertexPacket.fields X (oldSite X v) old A older cap c.privateMem childFit.le
  have new' := RefreshVertexPacket.parent_fields X (oldSite X v) old A older cap c.privateMem Y (promotedSites v)
    new parent before strideBound parentFit newData
  have stack' := (regs' (dfs 6) (fun ⟨i,e⟩ => apartD i 6 e)).trans stack
  have siteFit : id.val < 2^bits := by
    have startBefore : id.val ≤ address cap (layerBase cap base (initial :: ls.map Prod.fst) j) id :=
      (Nat.le_mul_of_pos_left _ (by omega : 0 < cap+2)).trans (Nat.le_add_left ..)
    exact startBefore.trans_lt (node ▸ (c.reg (dfs 7)).isLt)
  have site' := (congrArg Fin.val located.owner).trans ((Nat.mod_eq_of_lt siteFit).trans selected)
  obtain ⟨out,es,bodyRun,len,probes,choices,branch,pers,frame,kept,hits⟩ :=
    TraversalPlan.map_body B ties stride order bodyLoc dfs saved bodyBank done M X choice v degree n rowEnd U V m
      start parent child listHead (levelHead M.publicData m level).val (levelHead M.publicData m (level+1)).val old new
      (RefreshVertexAssembly.body_linked S.portExponent body locator loc dfs saved reg done M installed)
      (fun _ i => apartD _ i) (fun _ i => apartS _ i) mid atBody stack' (mem ▸ geom')
      (congrArg Fin.val located.oldHead) (congrArg Fin.val located.state.current) site' (congrArg Fin.val located.state.node)
      levelData row lanes stored oldCols newCols (mem ▸ old') (mem ▸ new') childBound parentBound oldDegree newDegree
      oldWidth newWidth copyBound large five capacity wide tableWidth
  let events := RefreshVertexAssembly.inputTrace S.portExponent X (oldSite X v) old U m listHead M.publicData
    (c.reg (dfs 7)) level later
  obtain ⟨time,cost,bs⟩ := RefreshVertexAssembly.inputTrace_cost S.portExponent X (oldSite X v) old U m listHead
    M.publicData (c.reg (dfs 7)) level later
  have join : ChildScan.Prefix M m c out oldBits (events++es) := by simpa only [List.append_nil] using front.trans bodyRun
  refine ⟨out,events++es,join,?_,?_,?_,branch,pers.trans per,?_,?_,?_⟩
  ·
    rw [PrimedInputRAM.Flow.choiceBits_append,choices,List.append_nil]; exact bs
  · rw [List.length_append]; exact Nat.add_le_add time.le len
  · rw [countProbes_append]; exact Nat.add_le_add cost.le probes
  · intro q hq
    exact (frame q (fun _ eqn => hq ⟨_,eqn.symm⟩)).trans (regs' q hq)
  · intro q hq hn
    exact (kept q hq hn).trans (congrFun mem q)
  · intro l
    have hval : (word (bits := bits) (histBase+l.val)).val = histBase+l.val :=
      Nat.mod_eq_of_lt ((Nat.add_lt_add_left l.isLt _).trans histFits)
    have oldAt := RefreshVertexPacket.outside X (oldSite X v) old A older cap c.privateMem childFit.le
      (word (histBase+l.val)) (Or.inr ((oldEnd.trans (Nat.le_add_right histBase l.val)).trans hval.symm.le))
    exact (hits l).trans (congrArg (fun q => q+_) ((congrFun mem _).trans oldAt))

end PairSimulation.RefreshVertex

end VPVNP
end Computability
end OAI
