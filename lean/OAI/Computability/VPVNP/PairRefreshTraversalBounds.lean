import OAI.Computability.VPVNP.PairRefreshTraversalAction
import OAI.Computability.VPVNP.PairVertexLevelBounds
import OAI.Computability.VPVNP.CompressorBlockLevelFit
import OAI.Computability.VPVNP.CompressorBlockShrinkPrefixFits
import OAI.Computability.VPVNP.CompressorRefreshTraversalChild
import OAI.Computability.VPVNP.PairShrinkCallCapacity
import OAI.Computability.VPVNP.PairShrinkGeometryLimit

/-!
# Bounds for the selected degree-refresh traversal

The old and new incidence heads use the actual row counts in the scheduled block
layout. The packed table of terms and segment widths also ends in that allocation.
The private map capacity uses the end of the selected DFS rows in the chronological
directory. The threshold is uniform in the coefficient specialization and branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalPlan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe PairSimulation NodeArguments NewSlots RefreshMapOperands DescriptorSpace
open MotifConversion NetworkKernel LocalHistory CursorBounds CursorNetwork TraversalRows Filter
open private refreshNext_width_bound from OAI.Computability.VPVNP.RefreshHistory
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

private theorem positions_formula {a g : ℕ} (Z : State a g) :
    Fintype.card Z.Base * 2^g = Z.positions := by
  simp only [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv _),Fintype.card_fin]

private theorem block_column {a l bits start positions blocks : ℕ} (Z : State a l)
    (level : Fin (BlockProgram.layout B start positions blocks).levels)
    (size : Z.positions ≤ positions) (degree : 2^a ≤ slotDegree S) (c : Fin 6) :
    let L := BlockProgram.layout B start positions blocks
    let rows := Z.positions * 2^a
    ((packedIncidence L bits level rows).column c).val + Fintype.card Z.Base * 2^l * 2^a ≤
      endAddress L := by
  intro L rows
  rw [positions_formula]
  have cap : rows ≤ slotCapacity L := Nat.mul_le_mul size degree
  have before := ShrinkBranch.incidence_before L bits level rows (0 : Fin 6) cap c
  exact before.trans ((Nat.le_add_right ..).trans
    ((tableEnd_le_nextLevel L level (0 : Fin 6)).trans (levelStart_mono L level.isLt)))

variable {g bits : ℕ} (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh)
  (start positions blocks : ℕ)
local notation "Y" => dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order))
  B.refresh S.port_order (And.right S.degree_bounds) choice
local notation "space₀" => BlockProgram.layout B start positions blocks
variable (prev next : Fin (BlockProgram.layout B start positions blocks).levels)
local notation "oldRows" => X.positions*2^S.portExponent
local notation "newRows" => State.positions Y*2^(S.degreeExponent 0)
local notation "U" => packedIncidence space₀ bits prev oldRows
local notation "V" => packedIncidence space₀ bits next newRows
local notation "s" => RefreshBlockPlan.shape B
local notation "P" => Allocation.plan X (S.degreeExponent 0) (LevelRecipe.Shape.dH s) (LevelRecipe.Shape.ties s) (LevelRecipe.Shape.stride s) (arrayBase space₀ prev)

set_option maxHeartbeats 1800000 in
/-- Bounds used by the canonical probe proof, including both distinct incoming
and width columns. Every endpoint follows from the actual old position count. -/
theorem layout_limits (size : X.positions ≤ positions) {limit : ℕ}
    (fit : endAddress space₀ < 2^bits) (below : endAddress space₀ ≤ limit) :
    levelStart space₀ prev+60 < limit ∧ levelStart space₀ next+59 < limit ∧ (P).supply ≤ limit ∧
      (∀ c : Fin 6, ((U).column c).val + Fintype.card X.Base*2^(S.portExponent+g)*2^S.portExponent ≤ limit) ∧
      (∀ c : Fin 6, ((V).column c).val + Fintype.card (State.Base Y)*2^g*2^(S.degreeExponent 0) ≤ limit) ∧
      Fintype.card X.Base*2^S.portExponent*2^g*2^S.portExponent ≤ 2^bits ∧
      2^g < 2^bits ∧ 2^S.portExponent < 2^bits := by
  have stop := (BlockLevelFit.refresh (L := space₀) (w := bits) (g := g) B start positions blocks prev rfl X size fit).1.next
  simp only [BlockLevelFit.tableStart,Nat.zero_mul,Nat.add_zero] at stop
  have supply : (P).supply ≤ (P).stop :=
    (((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have header (i : Fin (space₀).levels) : levelStart space₀ i+60 < endAddress space₀ := by
    have hlen : 60 < levelWords space₀ :=
      (by decide : 60 < 66).trans_le ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
    have hnext : levelStart space₀ i + levelWords space₀ = levelStart space₀ (i.val+1) := by
      simp only [levelStart,Nat.succ_mul,Nat.add_assoc]
    exact ((Nat.add_lt_add_left hlen _).trans_eq hnext).trans_le (levelStart_mono space₀ i.isLt)
  have oldDegree : 2^S.portExponent ≤ slotDegree S := le_max_left ..
  have newDegree : 2^S.degreeExponent 0 ≤ slotDegree S :=
    (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j) (Finset.mem_univ 0)).trans
      (le_max_right ..)
  have newSize := (dyadicRefreshNext_positions X S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh S.port_order S.degree_bounds.2 choice).le.trans size
  have cols (c : Fin 6) := block_column (bits := bits) (start := start) (positions := positions) (blocks := blocks) B X prev size oldDegree c
  have count : Fintype.card X.Base*2^(S.portExponent+g)*2^S.portExponent < 2^bits :=
    (Nat.le_add_left ..).trans_lt ((cols 0).trans_lt fit)
  have count' := count
  rw [pow_add,← Nat.mul_assoc] at count'
  have pos : 0 < Fintype.card X.Base := Fintype.card_pos
  have lanes : 2^g ≤ Fintype.card X.Base * 2^S.portExponent * 2^g :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos pos (Nat.two_pow_pos _))
  have left : 0 < Fintype.card X.Base * 2^S.portExponent * 2^g :=
    Nat.mul_pos (Nat.mul_pos pos (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
  exact ⟨(header prev).trans_le below,(Nat.add_lt_add_left (by decide : 59 < 60) _).trans ((header next).trans_le below),
    supply.trans (stop.trans ((levelStart_mono space₀ prev.isLt).trans below)),fun c => (cols c).trans below,
    fun c => (block_column (bits := bits) (start := start) (positions := positions) (blocks := blocks) B Y next newSize newDegree c).trans below,count'.le,
    (lanes.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))).trans_lt count',
    (Nat.le_mul_of_pos_left _ left).trans_lt count'⟩

variable {hist : ℕ} (order : B.Entry ≃ Fin hist)
  (v : (X.Base × BitWord g) × Fin (2^S.portExponent)) (A : Arena) (m : Memory bits)
  (parent child listHead histBase : ℕ) (G : W bits)
local notation "T" => plan B (RefreshBlockPlan.order B) (LevelRecipe.Shape.stride s) order
local notation "pub" => operands (Fin.val (sites (D := 2^S.portExponent) X.baseIndex (bitWordFinEquiv g) v))
  parent (levelStart space₀ next) histBase G
local notation "st" => word (bits := bits) (levelStart space₀ prev)

set_option maxHeartbeats 1800000 in
/-- Physical header and singleton row reads suffice for the entire fixed
expression family on a selected refresh stage of the chronological block. -/
theorem layout_reads (size : X.positions ≤ positions) {limit : ℕ} (fit : endAddress space₀ < 2^bits)
    (below : endAddress space₀ ≤ limit) (fits : limit ≤ 2^bits)
    (header : TraversalHeaders.Geometry (Fintype.card X.Base) g (levelStart space₀ prev) (levelStart space₀ next)
      (arrayBase space₀ prev) A U V m)
    (row : DFS.Row m parent listHead [word child]) (hp : parent < limit) (hl : listHead < limit)
    (old : (U).ActualColumns X m) (new : (V).ActualColumns Y m) :
    let ok := Expr.ReadsFrom (· < limit) pub st m
    (∀ i, ok ((T).diagonal i)) ∧ (∀ i, ok ((T).route i)) ∧ ok (T).directory ∧
      ∀ idx j, ok ((T).family.fields idx j) := by
  obtain ⟨prevHead,nextHead,area,oldCols,newCols,rows,lanes,ports⟩ :=
    layout_limits B X choice start positions blocks prev next size fit below
  exact canonical_reads B (RefreshBlockPlan.order B) (s).stride order X choice v A U V m (arrayBase space₀ prev)
    parent child listHead (levelStart space₀ prev) (levelStart space₀ next) histBase G (fit := rows)
    header row lanes old new limit fits prevHead nextHead hp hl area (oldCols 4) (oldCols 5)
    (newCols 4) (newCols 5) ports le_rfl

set_option maxHeartbeats 1800000 in
/-- Every read of the actual local action, including the selected map call,
avoids the terminal controller cells in the compiled block layout. -/
theorem layout_worker_reads (degree n rowEnd : ℕ)
    (room : Room B X choice v degree n rowEnd child parent hist bits)
    (old : X.network.Half (oldSite X v)) (new : (Y).network.Half (promotedSites v))
    (terminal : W bits) (terminalFit : terminal.val+31 < 2^bits)
    (size : X.positions ≤ positions) (below : endAddress space₀ ≤ terminal.val)
    (header : TraversalHeaders.Geometry (Fintype.card X.Base) g (levelStart space₀ prev) (levelStart space₀ next)
      (arrayBase space₀ prev) (TerminalLayout.privateRegions degree n rowEnd hist).arguments U V m)
    (row : DFS.Row m parent listHead [word child]) (hp : parent < terminal.val) (hl : listHead < terminal.val)
    (oldCols : (U).ActualColumns X m) (newCols : (V).ActualColumns Y m) :
    SourceTransport.Reads (TerminalLink.workerCell terminal)
      (canonicalEvents B (RefreshBlockPlan.order B) (s).stride order X choice v degree n rowEnd child parent
        room old new m (levelStart space₀ prev) (levelStart space₀ next) G) := by
  obtain ⟨prevHead,nextHead,area,oldEnds,newEnds,rows,lanes,ports⟩ :=
    layout_limits B X choice start positions blocks prev next size (below.trans_lt terminal.isLt) below
  exact canonical_worker_reads B (RefreshBlockPlan.order B) (s).stride order X choice v degree n rowEnd child parent
    room old new m (levelStart space₀ prev) (levelStart space₀ next) G U V (arrayBase space₀ prev) listHead (fit := rows)
    header row lanes oldCols newCols terminal terminalFit prevHead nextHead hp hl area (oldEnds 4) (oldEnds 5)
    (newEnds 4) (newEnds 5) ports le_rfl

/-- Map capacity up to the cache of the actual chronological layout. The row
count comes from the same selected execution as the graph and node operands. -/
theorem eventually_selected_capacity (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    {workspace : ℕ → ℕ} (bounded : PolynomiallyBounded workspace) (degree labels : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (split : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (R : Type*) [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f),
      let Z := pairInput S split hD
      let count := blockCount (u.θ : ℝ) n
      let space := BlockProgram.layout B (workspace n) (initialPositions b n) count
      ∀ z : (B.execute f hf count hT Z).Choices,
        let rows := words B.recordLimit (selectedLayers B f hf count hT Z z)
        MapWorkspace.Capacity B.refresh (wordBits b n) n
          (TerminalLayout.privateRegions degree n (endAddress space+rows) labels).cacheBase := by
  let bound n := NativeFrame.histLimit degree b workspace n + labels + n^5
  have hBound : PolynomiallyBounded bound :=
    ((NativeFrame.histLimit_bounded degree b bounded).add (.const labels)).add (PolynomiallyBounded.id.pow 5)
  have hb' : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  filter_upwards [NativeFrame.eventually_selected_histBase B u (BlockProgram.allocationShape B) b hb bounded,
    MapWorkspace.eventually_capacity (B := B.refresh) b hb' bound hBound] with n selected cap
  intro base lanes split hD hT R _ f hf Z count space z rows
  let full := cursorLayout (BlockProgram.allocationShape B) b S.steps u.θ (workspace n) n
  have prior : endAddress space ≤ endAddress full := BlockProgram.allocation_end B _ _ count
  have upper := selected split hD hT R f hf z degree labels
  let actual := TerminalLayout.privateRegions degree n (endAddress space+rows) labels
  have actualLe : actual.cacheBase ≤ bound n := by
    refine Nat.add_le_add_right (Nat.add_le_add_right (le_trans ?_ upper) labels) _
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.add_le_add_right prior rows)) n
  exact ⟨cap.selectorBits,cap.demandBits,cap.payloadBits,actualLe.trans_lt cap.room,
    fun a ha => cap.fields a (ha.trans actualLe)⟩

/-- Every selected refresh stage fits its old and new half-wire widths and the
motif repetition count at the same length threshold. -/
theorem eventually_selected_sizes (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (split : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (R : Type*) [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f),
      let Z := pairInput S split hD
      let count := blockCount (u.θ : ℝ) n
      ∀ (z : (B.execute f hf count hT Z).Choices) {g : ℕ}
        (X : State S.portExponent (S.portExponent+g))
        (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
          (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (record : List Bool),
        RefreshPlacement.traversalLevel f hf X choice record ∈ executeLevels B f hf count hT Z z →
        X.positions ≤ initialPositions b n ∧ X.maxWireWidth ≤ n ∧
          (dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
            B.refresh S.port_order S.degree_bounds.2 choice).maxWireWidth ≤ n ∧
          ∀ p : X.Base × BitWord g, repetitions B.refresh
            (blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) p) ≤ n := by
  let K := refreshLengthConstant S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 B.refresh
  filter_upwards [ShrinkCallCapacity.eventually_levels B u b hb K] with n bounds
  intro base lanes split hD hT R _ f hf Z count z g X choice record member
  obtain ⟨pos,width⟩ := bounds split hD hT R f hf z (RefreshPlacement.traversalLevel f hf X choice record) member
  change K * (X.maxWireWidth + 1) ≤ n at width
  have kpos : 1 ≤ K := le_max_left ..
  refine ⟨pos,((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ kpos)).trans width,?_,?_⟩
  · apply Finset.sup_le
    intro e _
    exact (refreshNext_width_bound X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
      B.refresh S.port_order S.degree_bounds.2 (by linarith [S.portComparison_pos]) choice e).trans width
  · intro p
    apply le_trans (term_repetitions_le B.refresh _ (W := X.maxWireWidth) ?_) ((Nat.mul_le_mul ?_ (Nat.le_succ _)).trans width)
    · intro e
      unfold blockDemandWidths internalWidth
      split <;> exact X.width_le_maxWireWidth _
    · exact (le_max_left ..).trans (le_max_right ..)

open TraversalRoles

/-- A refresh uses the same ordinal in the preceding layer. Its parent header,
unique child pointer and child header are all inside the actual row interval. -/
theorem refresh_row_bounds {cap first stage : ℕ} (positive : 1 ≤ cap) (tags : List TaggedLayer)
    (j : Fin tags.length) (hj : j.val = stage+1) (i : Fin tags[j].layer.count) :
    let parent := address cap (layerBase cap first tags j.val) i.val
    let child := address cap (layerBase cap first tags stage) i.val
    let rowEnd := first + tagWords cap tags
    child ≤ parent ∧ parent+2 < rowEnd := by
  intro parent child rowEnd
  have before := VertexLevelBounds.layerBase_mono cap first tags (by omega : stage ≤ j.val)
  have after := VertexLevelBounds.layerBase_mono cap first tags j.isLt
  have endEq : layerBase cap first tags tags.length = rowEnd := by simp [layerBase,rowEnd,tagWords]
  rw [endEq,VertexLevelBounds.layerBase_succ cap first tags j] at after
  have inside := Nat.mul_le_mul_left (cap+2) i.isLt
  rw [Nat.mul_succ] at inside
  exact ⟨Nat.add_le_add_right before _,by
    change layerBase cap first tags j.val + (cap+2)*i.val + 2 < rowEnd
    change layerBase cap first tags j.val + (cap+2)*tags[j].layer.count ≤ rowEnd at after
    omega⟩

/-- The complete private and physical bounds for the selected map role. The
child and parent row addresses use the actual site ordinal in adjacent layers. -/
theorem eventually_selected_room (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    {workspace : ℕ → ℕ} (bounded : PolynomiallyBounded workspace) (hist : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (split : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (R : Type*) [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f),
      let Z := pairInput S split hD
      let count := blockCount (u.θ : ℝ) n
      let space := BlockProgram.layout B (workspace n) (initialPositions b n) count
      ∀ (z : (B.execute f hf count hT Z).Choices) {g : ℕ}
        (X : State S.portExponent (S.portExponent+g))
        (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
          (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (record : List Bool)
        (stage : Fin (executeLevels B f hf count hT Z z).length),
        (executeLevels B f hf count hT Z z)[stage] = RefreshPlacement.traversalLevel f hf X choice record →
        let tags := selected B f hf count hT Z z
        let first := endAddress space
        let rowEnd := first + words B.recordLimit (selectedLayers B f hf count hT Z z)
        ∀ (j : Fin tags.length) (_ : j.val = stage.val+1) (i : Fin tags[j].layer.count)
          (v : (X.Base × BitWord g) × Fin (2^S.portExponent)),
          let child := address B.recordLimit (layerBase B.recordLimit first tags stage.val) i.val
          let parent := address B.recordLimit (layerBase B.recordLimit first tags j.val) i.val
          X.positions ≤ initialPositions b n ∧ parent+2 < rowEnd ∧
            Room B X choice v (slotDegree S) n rowEnd child parent hist (wordBits b n) := by
  have hb' : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  let K := MapCallWords.headCapacity (2^S.portExponent) (2^S.expanderExponent)
  filter_upwards [eventually_selected_capacity B u b hb bounded (slotDegree S) hist,
    eventually_selected_sizes B u b hb, MapConstants.eventually_width B.refresh b hb',
    eventually_ge_atTop (K+12), eventually_ge_atTop 5] with n capacity sizes table large five
  intro base lanes split hD hT R _ f hf Z count space z g X choice record stage step tags first rowEnd j hj i v child parent
  have member : RefreshPlacement.traversalLevel f hf X choice record ∈ executeLevels B f hf count hT Z z := by
    rw [← step]; exact List.getElem_mem stage.isLt
  obtain ⟨pos,oldWidth,newWidth,copies⟩ := sizes split hD hT R f hf z X choice record member
  have cap := capacity split hD hT R f hf z
  have eqn : first+tagWords B.recordLimit tags = rowEnd := by
    rw [tagWords,show tags.map TaggedLayer.layer = _ from selected_layers B f hf count hT Z z]
  have ⟨childBefore,parentEnd⟩ := refresh_row_bounds (first := first) (le_max_left 1 _ : 1 ≤ B.recordLimit) tags j hj i
  change child ≤ parent at childBefore
  change parent+2 < first+tagWords B.recordLimit tags at parentEnd
  rw [eqn] at parentEnd
  exact ⟨pos,parentEnd,by
    refine ⟨by omega,by omega,le_max_left ..,?_,oldWidth,newWidth,copies v.1,large,five,cap,table⟩
    exact (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j) (Finset.mem_univ 0)).trans
      (le_max_right ..)⟩

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI
