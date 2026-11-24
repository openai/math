import OAI.Computability.VPVNP.LiveVirtualPairOccurrence
import OAI.Computability.VPVNP.LiveVirtualPairPaperDescriptor
import OAI.Computability.VPVNP.LiveVirtualPairShadowCapacity
import OAI.Computability.VPVNP.PairTerminalVertexPackedShadow
import OAI.Computability.VPVNP.PairVertexRootEntry
import OAI.Computability.VPVNP.PairTerminalFootprint

/-! # The cursor leaf's header and auxiliary reset words at a selected vertex -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression
open CompressorRecords DescriptorSpace CursorNetwork CursorBounds LocalHistory TraversalRows
open CutSchedule ExponentTrace
open scoped Fin.CommRing
set_option quotPrecheck false

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {D : FixedProgramDiagonal.Program}
  {B : S.Templates} {u : PairExponents B.growthConstant}
  {n : ℕ} {hn : 2 ≤ n} {ht : 21 ≤ 2 ^ (D.geometry n).w} {clk : 44 ≤ n ^ 10000}
  (V : D.VirtualPairs B u hn D.constants.circuitExponent)
  (adv : Bits (n ^ D.constants.advicePower))
  (ξ : Exterior (D.chainHeight n) (n ^ D.constants.deltaPower))
  (i : D.groupIndices n) (μ : PairStages.Group.Nominations.Nom (D.executionGroup n ht clk))

local notation "grp" => D.executionGroup n ht clk
local notation "pub" => terminalOperands grp
local notation "H" => vertexHeader grp
local notation "W" => (D.geometry n).w
local notation "aux" => V.data adv ξ i (physicalNomination rfl μ)
local notation "l" => reservedLanes B u n
local notation "b" => virtualBits D.addressFactor n - reservedLanes B u n

/-- The actual header words loaded at a site, and the range and contents of its
shadow bank. Every address read by a cursor leaf avoids both terminal controls. -/
structure VirtualPairs.CursorLeafHeader (m : Memory W) : Prop where
  stride : (m (H + 15).val).val = B.recordLimit + 2
  radixB : (m (H + 18).val).val = 2 ^ b
  radixL : (m (H + 19).val).val = 2 ^ l
  span : (m (H + 20).val).val = LiveAuxiliaryHeaders.span (D.pairLengths i) (aux).hist.length
  shadowRoom : (pub 3).val + (m (H + 20).val).val ≤ 2 ^ W
  shadowData : ∀ j < (m (H + 20).val).val, (m ((pub 3).val + j)).val = ((aux).initial j).val
  shadowSafe : ∀ j < (m (H + 20).val).val, TerminalLink.workerCell H ((pub 3).val + j)

/-- The ten operands reloaded from the site's private geometry carry the same
shadow, radix and stride facts into the native leaf front. -/
theorem VirtualPairs.CursorLeafHeader.operands
    {m : Memory W} (h : V.CursorLeafHeader adv ξ i μ m) (role : BurstRAM.Word W)
    {p r k : ℕ} (pc : LeafImage.Label → Fin p) (reg : LeafImage.Reg ↪ Fin r)
    (port : LeafImage.Pub → Fin k) (ret : Fin p) (M : PrivateRAM.Machine W p r k)
    (assigned : M.publicData ∘ port = NativeFrame.leafWords (slotDegree S) pub H role m ∘
      LeafGeometryLoad.slot) (length : (pub 6).val = n) :
    LeafFront.Operands (LeafImage.front pc reg port ret) M m aux
      (NativeFrame.fromHeader (slotDegree S) pub H m) b l B.recordLimit ∧
    M.publicData (port .size) = (n : BurstRAM.Word W) :=
  NativeFrame.leaf_operands (slotDegree S) pub H role m pc reg port ret M assigned aux
    b l B.recordLimit h.stride h.radixB h.radixL h.span h.shadowRoom h.shadowData length

local notation "X" => V.scanState
local notation "T" => blockCount (u.θ : ℝ) n
variable {A : Type*} [CommRing A] {f : B.Entry → A} {ok : B.IsSolution f}
  {z : (B.execute f ok (blockCount (u.θ : ℝ) n) le_rfl V.scanState).Choices}
  {L : DescriptorSpace.Layout} {tab : Fin L.shape.tables}
  {ord : ℕ} {calendar reference m : Memory (D.geometry n).w}
local notation "Y" => (B.execute f ok T le_rfl X).finalState z
local notation "ls" => selectedLayers B f ok T le_rfl X z
local notation "tags" => TraversalRoles.selected B f ok T le_rfl X z

attribute [local irreducible] BlockSchedule.Templates.execute CursorNetwork.cursorState
  CursorBounds.wordBits

local notation "phySpan" => LiveAuxiliaryHeaders.span
  (PairStages.Group.Auxiliary.pairLengths grp (physicalPairIndex i)) (histLength grp)

set_option maxHeartbeats 1200000 in
-- Elaborating the selected execution identifies its physical and virtual word widths.
/-- The preserved post-copy descriptor and shadow at calendar entry suffice for
all selected vertex ordinals, including after prior motif counter updates. -/
theorem VirtualPairs.cursorLeafHeader_of_calendar
    {bits : Fin (Y).totalWidth → Bool}
    (P : VertexPacked grp L B.recordLimit tags (Y).totalWidth)
    (entry : TerminalProgram.VertexEntry B f ok T le_rfl X z L tab b l pub
      calendar reference bits)
    (later : LinkedVertexMemory grp reference ord m)
    (descriptor : TerminalBootstrap.shadowSpan pub calendar =
      ((phySpan : ℕ) : BurstRAM.Word W))
    (reset : ∀ j < phySpan,
      calendar ((pub 3).val + j) = (aux).initial j) :
    V.CursorLeafHeader adv ξ i μ m := by
  have vd := V.cap.capFits
  rw [← pow_add] at vd
  have dw : virtualBits D.addressFactor n + roundedUp 1 4 n < W :=
    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp vd
  have lanes := V.lanes
  have bFit := Nat.pow_lt_pow_right Nat.one_lt_two (show b < W by omega)
  have lFit := Nat.pow_lt_pow_right Nat.one_lt_two (show l < W by omega)
  have pos : 0 < (siteOrder X).length :=
    (show 0 < Fintype.card (X).network.Site from (X).positions_pos).trans_eq
      ((Fintype.card_congr (siteOrder X).entries).symm.trans (Fintype.card_fin _))
  have strideLe : B.recordLimit + 2 ≤ TraversalRoles.tagWords B.recordLimit tags := by
    apply Nat.le_mul_of_pos_right
    simp only [TraversalRoles.selected, List.map_cons, List.sum_cons]
    exact Nat.add_pos_left pos _
  let len := phySpan
  have hn₁ : 1 ≤ (grp).g.n := by change 1 ≤ n; omega
  have cap := V.shadowCapacity (ht := ht) (hf := clk) rfl (physicalPairIndex i)
  rw [LiveProgram.Layout.virtualSiteBits_eq (D.geometry n) (show 1 ≤ n by omega)] at cap
  have extent : (pub 3).val + len ≤ (pub 2).val := shadow_span_room grp _ hn₁ P.fit cap
  have small : len < 2 ^ W := (Nat.le_add_left len _).trans_lt (extent.trans_lt (pub 2).isLt)
  have hist : (aux).hist.length = histLength grp :=
    List.length_ofFn.trans (physicalGrammarCount (ht := ht) (hf := clk) (D := D) rfl).symm
  have size : len = LiveAuxiliaryHeaders.span (D.pairLengths i) (aux).hist.length := by
    rw [hist,← physicalPairLengths (ht := ht) (hf := clk) i]
  let data := TerminalBootstrap.fromState L (ls).dropLast B.recordLimit b l (Y) tab
  have field (j : Fin 21) (lo : 0 < j.val) (t : j.val ≠ 12) (r : j.val ≠ 14) :
      m (H + (j.val : BurstRAM.Word (grp).g.w)).val =
        TerminalBootstrap.values L (ls).dropLast.length data B.recordLimit pub calendar j :=
    (P.header later _ lo (j.isLt.trans (by decide))).trans (entry.packedField P j lo t r)
  have pitch : m (H + 15).val = ((B.recordLimit + 2 : ℕ) : BurstRAM.Word W) :=
    field 15 (by decide) (by decide) (by decide)
  have base : m (H + 18).val = ((2 ^ b : ℕ) : BurstRAM.Word W) :=
    field 18 (by decide) (by decide) (by decide)
  have lane : m (H + 19).val = ((2 ^ l : ℕ) : BurstRAM.Word W) :=
    field 19 (by decide) (by decide) (by decide)
  have count : m (H + 20).val = TerminalBootstrap.shadowSpan pub calendar :=
    field 20 (by decide) (by decide) (by decide)
  have countVal : (m (H + 20).val).val = len :=
    (congrArg Fin.val (count.trans descriptor)).trans (Nat.mod_eq_of_lt small)
  have wordVal {j : ℕ} {v : BurstRAM.Word W} (eqn : v = (j : BurstRAM.Word W))
      (bound : j < 2 ^ W) :
      v.val = j := eqn ▸ Nat.mod_eq_of_lt bound
  have lower (j : ℕ) : L.base ≤ levelStart L j := by
    simp only [levelStart, levelsBase, directoryBase, plannerTag, frameBase]
    omega
  have first : L.base ≤ endAddress L := lower L.levels
  have bank : L.base ≤ DescriptorSpace.tableBase L (ls).dropLast.length tab := by
    apply (lower (ls).dropLast.length).trans
    simp only [DescriptorSpace.tableBase, arrayBase, incidenceStart]
    omega
  have room : (H).val + 32 ≤ 2 ^ W := P.room
  have arena := P.arena
  have ws := P.workspace
  refine ⟨wordVal pitch (by omega), wordVal base bFit, wordVal lane lFit, countVal.trans size,
    countVal ▸ (extent.trans (pub 2).isLt.le), ?_, ?_⟩
  · intro j hj
    rw [countVal] at hj
    have low : (pub 3).val + j < L.base := by omega
    have old := entry.raw _ (low.trans_le first) (.inl (low.trans_le bank))
    exact congrArg Fin.val (((P.shadow later _ hn₁ cap hj).trans old).trans (reset j hj))
  · intro j hj
    rw [countVal] at hj
    apply TerminalFootprint.below H
    · change (H).val + 31 < 2 ^ W
      omega
    · omega

variable {initial : Memory (D.geometry n).w}
  {N : PairStages.Group.Indexed (D.executionGroup n ht clk) Stage.nominations initial
    (PairStages.Group.Nominations.Nom (D.executionGroup n ht clk))}

set_option maxHeartbeats 1200000 in
-- Elaborating the selected execution identifies its physical and virtual word widths.
/-- Instantiate the cursor header from the real sparse-copy branch and the
low-address frame of the startup and online calendar. -/
theorem VirtualPairs.cursorLeafHeader
    (prepared : PreparedBranch grp initial (physicalPairIndex i)
      ((physicalPairLengths (ht := ht) (hf := clk) i).symm ▸ PairedChain.headers adv ξ i) N μ)
    {bits : Fin (Y).totalWidth → Bool}
    (P : VertexPacked grp L B.recordLimit tags (Y).totalWidth)
    (entry : TerminalProgram.VertexEntry B f ok T le_rfl X z L tab b l pub
      calendar reference bits)
    (later : LinkedVertexMemory grp reference ord m)
    (low : ∀ x < (pub 2).val, x ≠ (PairTag.address pub).val →
      calendar x = prepared.copy.memory () x) :
    V.CursorLeafHeader adv ξ i μ m := by
  apply V.cursorLeafHeader_of_calendar adv ξ i μ P entry later
  · exact prepared.shadowSpan_of_cell
      (low _ (histogramTarget_lt_workspace grp P.fit) (histogramCell_lt_tag grp P.fit).ne)
  · intro j hj
    have hn₁ : 1 ≤ (grp).g.n := by change 1 ≤ n; omega
    have cap := V.shadowCapacity (ht := ht) (hf := clk) rfl (physicalPairIndex i)
    rw [LiveProgram.Layout.virtualSiteBits_eq (D.geometry n) (show 1 ≤ n by omega)] at cap
    have range := shadow_span_room grp (physicalPairIndex i) hn₁ P.fit cap
    have before := pairTag_lt_shadow grp P.fit
    exact (low _ (by omega) (by omega)).trans (V.shadow_initial rfl adv ξ i μ prepared j)

end FixedProgramDiagonal.Program


namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds BurstRAM LiveProgram CompressedPair CompressorRecords
set_option quotPrecheck false
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
  {u : PairExponents B.growthConstant} {D : FixedProgramDiagonal.Program} {C n : ℕ} {hn : 2 ≤ n}
  {V : D.VirtualPairs B u hn C} {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
  {c : Constants} {labels : c.motifLabels = Fintype.card B.Entry} {base clk rate : ℕ}
  {pub : Fin 11 → Word (wordBits D.addressFactor n)} {m : Memory (wordBits D.addressFactor n)}

local notation "boot" => paperBootstrap B u
local notation "A" => BlockProgram.script B
local notation "entry" => after m (eventLog (cursorStartupLogs boot pub D.addressFactor n base m
  (A).initial.length (A).block.length (A).size))

attribute [local irreducible] BlockProgram.script BlockProgram.layout CursorNetwork.cursorState
  CompressedPair.stages CompressedPair.regs PairSimulation.TerminalProgram.workers

/-- At the selected online handoff, the startup and calendar preserve each low
word except the pair tag written by the stage transfer. -/
theorem VirtualPairs.PaperDescriptor.post_below
    (Y : V.PaperDescriptor f hf c labels base clk rate pub m)
    (runs : TransferredStartup.Runs (bootstrapRows boot (A).initial.length (A).block.length)
      (A).size (startupLayout boot (A).initial.length (A).block.length D.addressFactor n base)
      D.addressFactor n (S.degreeExponent 0) S.laneBits S.steps pub (PairTag.address pub) m)
    (workspace : (pub 2).val = base)
    (z : (B.execute f hf (blockCount (u.θ : ℝ) n) le_rfl V.scanState).Choices)
    (x : ℕ) (below : x < (pub 2).val) (apart : x ≠ (PairTag.address pub).val) :
    onlinePost (Y.paths z) x = m x := by
  let initial := Y.cursor.interval
  let whole := (initial.withTrace Y.result.trace).part z
  have stable := initial.withTrace_stable Y.result.trace Y.result.frame whole.run
  have keep : whole.memory x = entry x := by
    simpa only [BranchSegments.Segment.memory, List.take_length] using
      stable.take_eq whole.logs.length x (by omega)
  rw [Y.post z, writeMemory, ite_eq_right apart, ← initial.withTrace_memory Y.result.trace z]
  exact keep.trans
    (cursorStartup_after_below boot pub D.addressFactor n base m runs x (workspace ▸ below) apart)

end FixedProgramDiagonal.Program

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM LiveProgram LocalCount
open PairStages PairStages.Group PairStages.Group.CompressedPaths CompressedPair
open PairStages.Group.Auxiliary
open PairSimulation PairSimulation.LocalHistory CompressorRecords
open scoped Fin.CommRing
set_option quotPrecheck false

variable {D : FixedProgramDiagonal.Program} {n : ℕ}
  {ht : 21 ≤ 2 ^ (D.geometry n).w} {hc : 44 ≤ n ^ 10000}
  {K : Type} [Field K] {S : BlockSchedule K} {B : S.Templates} {hn : 2 ≤ n} {p : Nat.Primes}
  {M : Model p (B.compressorDegree n) (B.compressorEquations hn D.constants.circuitExponent)}
  {u : PairExponents B.growthConstant} (V : D.VirtualPairs B u hn D.constants.circuitExponent)
  (data : D.ScalarData B hn M)

local notation "G" => D.executionGroup n ht hc
variable (W : Conditions (D.executionGroup n ht hc) (2 ^ (D.geometry n).d) (D.geometry n).H)
  (P : PairStageConditions (D.executionGroup n ht hc) (2 ^ (D.geometry n).d) (D.geometry n).H)
  (hg : D.constants.motifLabels = Fintype.card B.Entry)
  (cut : 1 + B.denseCount n D.constants.circuitExponent * D.counterWidth n ≤
    n ^ D.constants.deltaPower)
  (I : VirtualPairs.PhysicalInput data W P rfl hg cut)

local notation "ext" => VirtualPairs.exterior data W P rfl hg cut I
local notation "idx" => VirtualPairs.modelIndex data W P rfl hg cut I
local notation "src" => I.branch.copy.memory ()
local notation "ws" => (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
local notation "ports" => publicWords G
local notation "f" => B.compressorValues hn M
local notation "ok" => B.compressorValues_solution hn M
local notation "T" => blockCount (u.θ : ℝ) n
local notation "X" => V.scanState
local notation "E" => B.execute f ok T le_rfl X
local notation "L" => BlockProgram.layout B ws (initialPositions D.addressFactor n) T
local notation "boot" => paperBootstrap B u
local notation "A" => BlockProgram.script B
local notation "l" => reservedLanes B u n
local notation "b" => virtualBits D.addressFactor n - reservedLanes B u n

set_option maxHeartbeats 1200000 in
-- The selected native descriptor and physical input share several dependent indices.
/-- The native leaf at a selected vertex reads the nominated input's reset words. -/
theorem VirtualPairs.cursorLeafHeader_of_paperDescriptor
    {rate : ℕ} (Y : V.PaperDescriptor f ok D.constants hg ws (fuel G) rate ports src)
    (setup : TransferredStartup.Runs (bootstrapRows boot (A).initial.length (A).block.length)
      (A).size
      (startupLayout boot (A).initial.length (A).block.length D.addressFactor n ws)
      D.addressFactor n (S.degreeExponent 0) S.laneBits S.steps ports (PairTag.address ports) src)
    (z : (E).Choices) {tab : Fin (L).shape.tables} {ord : ℕ} {reference m : Memory (G).w}
    {bits : Fin ((E).finalState z).totalWidth → Bool}
    (packed : VertexPacked G L B.recordLimit (TraversalRoles.selected B f ok T le_rfl X z)
      ((E).finalState z).totalWidth)
    (entry : TerminalProgram.VertexEntry B f ok T le_rfl X z L tab b l ports
      (onlinePost (Y.paths z)) reference bits)
    (later : LinkedVertexMemory G reference ord m) :
    V.CursorLeafHeader data.advice ext idx I.μ m := by
  have workspace : (ports 2).val = ws := Nat.mod_eq_of_lt packed.fit
  apply V.cursorLeafHeader_of_calendar data.advice ext idx I.μ packed entry later
  · exact I.branch.shadowSpan_of_cell (Y.post_below setup workspace z _
      (histogramTarget_lt_workspace G packed.fit) (histogramCell_lt_tag G packed.fit).ne)
  · intro j hj
    have hn₁ : 1 ≤ (G).g.n := by change 1 ≤ n; omega
    have cap := V.shadowCapacity (ht := ht) (hf := hc) rfl (physicalPairIndex idx)
    rw [LiveProgram.Layout.virtualSiteBits_eq (D.geometry n) (show 1 ≤ n by omega)] at cap
    have extent := shadow_span_room G (physicalPairIndex idx) hn₁ packed.fit cap
    have before := pairTag_lt_shadow G packed.fit
    exact (Y.post_below setup workspace z ((terminalOperands G 3).val + j)
      ((Nat.add_lt_add_left hj _).trans_le extent)
      (before.trans_le (Nat.le_add_right _ _)).ne').trans
      (V.input_shadow data W P rfl hg cut I j)

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
