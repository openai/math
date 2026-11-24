import OAI.Computability.VPVNP.PairVirtualCursorLeaf
import OAI.Computability.VPVNP.PairVertexRoleNativeLeaf

/-! # Native leaf execution on the virtual pair's scan state -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage.RoleDomains

open BurstRAM PrivateRAM CursorNetwork CursorRouting Compression DFS TreeDecode LeafStartup NativeFrame LocalHistory
open private scanInput from OAI.Computability.VPVNP.PairSimulationScanTrace
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}
    {geometry rootFields shrink refresh : Segment} {p r w : ℕ}
    (V : Placement (segments geometry rootFields LeafRole.segment shrink refresh) p r)
    (M : Machine w p r 11) {L : PrimedInputRAM.Lengths} {n a H s : ℕ}
    {Q : PrimedInputRAM.Layout L n a H w} (aux : PrimedCounter.Data Q s)
    {d b l e : ℕ} [NeZero d] (split : d = b+l) (dim : 1 < d) (cap : ProcessorBudget n d e w)
    (m : Memory w) (header offset : Word w) (arity rowCap rowBase : ℕ)

local notation "region" => fromHeader arity M.publicData header m
local notation "words" => leafWords arity M.publicData header offset m
local notation "numbering" => Equiv.trans (finCongr split) (cursorCoordinateLabels b l)
local notation "X" => scanInput numbering dim S e w

/-- On the scan's original coordinate numbering, the leaf handler accepts
and rejects exactly as its machine entry does on every stored cursor packet. -/
theorem nativeNumberedLeaf (link : Contains V M)
    (fit : (region).stackBase + Fintype.card ScalarPort*n^40 < 2^w)
    (resources : LeafVisit.CursorLeafBounds aux cap)
    (address : rowBase = (LeafRole.addressFields words .base).val)
    (stride : (m (header+15).val).val = rowCap+2)
    (radixB : (m (header+18).val).val = 2^b) (radixL : (m (header+19).val).val = 2^l)
    (span : (m (header+20).val).val = LiveAuxiliaryHeaders.span L aux.hist.length)
    (shadowFit : (M.publicData 3).val + (m (header+20).val).val ≤ 2^w)
    (headers : ∀ j < (m (header+20).val).val, (m ((M.publicData 3).val+j)).val = (aux.initial j).val)
    (size : (M.publicData 6).val = n) :
    (LeafRole.parser (endAddr := n) (b := d) (l := 0) words aux cap region fit m (n^39)).ExactOn
      (Leaf X rowCap rowBase region words offset (LeafVisit.cacheWords aux d e))
      M (V.entry .leaf) (V.dfsPC 3) V.dfs m := by
  subst d
  exact nativeLeaf aux dim (Nat.add_sub_of_le S.degree_bounds.1) V M cap m header offset
    arity rowCap (n^39) rowBase fit link address stride radixB radixL span shadowFit headers
    size resources.time resources.room

end PairSimulation.VertexImage.RoleDomains

namespace FixedProgramDiagonal.Program

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression CompressorRecords
open CursorNetwork CursorBounds VertexImage TreeDecode DFS CutSchedule ExponentTrace Filter LocalHistory TraversalRows
open scoped Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000

attribute [local irreducible] CursorBounds.wordBits CursorBounds.virtualBits BurstRAM.addressWidth

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates} {D : FixedProgramDiagonal.Program}
    {u : PairExponents B.growthConstant} {n : ℕ} {hn : 2 ≤ n} {p : Nat.Primes}
    {model : LabelEvaluator.Model p (B.compressorDegree n) (B.compressorEquations hn D.constants.circuitExponent)}
    {ht : 21 ≤ 2^(D.geometry n).w} {clk : 44 ≤ n^10000}
    [NeZero (virtualBits D.addressFactor n)]
    (V : D.VirtualPairs B u hn D.constants.circuitExponent) (scalar : D.ScalarData B hn model)
    (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)) (i : D.groupIndices n)
    (μ : PairStages.Group.Nominations.Nom (D.executionGroup n ht clk))
    {g : ℕ} (order : B.Entry ≃ Fin g) (z : (V.selection (M := model)).Choices)
    (m : Memory (D.geometry n).w)

local notation "group₀" => D.executionGroup n ht clk
local notation "pub" => terminalOperands group₀
local notation "header₀" => vertexHeader group₀
local notation "w₀" => (D.geometry n).w
local notation "dim₀" => virtualBits D.addressFactor n
local notation "lanes₀" => reservedLanes B u n
local notation "T₀" => blockCount (u.θ : ℝ) n
local notation "κ" => B.compressorValues hn model
local notation "ok" => B.compressorValues_solution hn model
local notation "L₀" => BlockProgram.layout B (pub 2).val V.scanState.positions T₀
local notation "rowBase" => DescriptorSpace.endAddress (L₀)
local notation "seg₀" => TerminalProgram.nativeSegments B D.constants D.numerator D.denominator order
local notation "V₀" => VertexImage.placement (seg₀)
local notation "M₀" => PrivateRAM.Template.instantiate (VertexImage.template (seg₀)) w₀ pub
local notation "aux" => V.data scalar.advice ξ i (physicalNomination (D := D) (n := n) (ht := ht) (hf := clk) rfl μ)
local notation "region" => NativeFrame.fromHeader (slotDegree S) pub header₀ m
local notation "offset" => m (header₀+14).val
local notation "words" => NativeFrame.leafWords (slotDegree S) pub header₀ offset m
local notation "cache" => LeafVisit.cacheWords aux dim₀ (roundedUp 1 4 n)
local notation "domain" => RoleDomains.Leaf V.scanState B.recordLimit (rowBase) region words offset cache

attribute [local irreducible] BlockSchedule.Templates.execute VertexImage.placement VertexImage.template
    CursorNetwork.cursorState NativeOperands.saved NativeOperands.capacity

/-- Success and rejection for the installed vertex machine at any leaf packet
of the selected virtual pair. Its cache contains the actual auxiliary data. -/
theorem VirtualPairs.cursorLeafExact (resources : LeafVisit.CursorLeafBounds aux V.cap)
    (head : V.CursorLeafHeader scalar.advice ξ i μ m)
    (arena : V.CursorLeafArena (ht := ht) (clk := clk) κ ok z m g) :
    (V.cursorLeafParser scalar ξ i μ m arena.fit).ExactOn
      domain
      M₀ ((V₀).entry .leaf) ((V₀).dfsPC 3) (V₀).dfs m :=
  RoleDomains.nativeNumberedLeaf (S := S) (Q := V.layout i) (d := dim₀) (b := dim₀-lanes₀)
    (l := lanes₀) (e := roundedUp 1 4 n) V₀ M₀ aux (Nat.sub_add_cancel V.lanes).symm
    V.dimension V.cap m header₀ offset (slotDegree S) B.recordLimit (rowBase)
    (template_contains (seg₀) pub) arena.fit resources arena.address head.stride
    head.radixB head.radixL head.span head.shadowRoom head.shadowData arena.size

variable {V scalar ξ i μ} (A : CanonicalScan scalar V ξ i (physicalNomination (D := D) (n := n)
  (ht := ht) (hf := clk) rfl μ)) (power scan : ℕ)

local notation "Y₀" => (V.selection (M := model)).finalState z
local notation "format" => SelectedPacketFormat B κ ok T₀ le_rfl V.scanState z (rowBase)
local notation "desc" => selectedDesc B κ ok T₀ le_rfl V.scanState z (rowBase)
local notation "guard" => TerminalLink.workerCell header₀

/-- At each reached vertex, the same private arena supplies both exact
execution on arbitrary nomination tapes and the selected cursor jobs. -/
def CanonicalScan.CursorLeafExactCalls : Prop :=
  ∀ {initial : Memory w₀} {N : PairStages.Group.Indexed group₀ Stage.nominations initial
      (PairStages.Group.Nominations.Nom group₀)}
    (prepared : PreparedBranch group₀ initial (physicalPairIndex i)
      ((physicalPairLengths (ht := ht) (hf := clk) i).symm ▸ PairedChain.headers scalar.advice ξ i) N μ)
    {calendar reference : Memory w₀} {tab : Fin (L₀).shape.tables} {bits : Fin (Y₀).totalWidth → Bool}
    {ord : ℕ},
    TerminalProgram.VertexEntry B κ ok T₀ le_rfl V.scanState z (L₀) tab (dim₀-lanes₀) lanes₀
      pub calendar reference bits →
    LinkedVertexMemory group₀ reference ord m →
    (∀ x < (pub 2).val, x ≠ (PairTag.address pub).val → calendar x = prepared.copy.memory () x) →
    ∃ fit : (region).stackBase + Fintype.card LeafStartup.ScalarPort*n^40 < 2^w₀,
      (V.cursorLeafParser scalar ξ i μ m fit).ExactOn domain M₀ ((V₀).entry .leaf) ((V₀).dfsPC 3) (V₀).dfs m ∧
      ∀ shrink refresh : HookParser w₀ n,
        SelectedCursorLeaf.Rows V₀ M₀
          (RoleDomains.handlers (V.cursorLeafParser scalar ξ i μ m fit) shrink refresh)
          m offset region words cache B.recordLimit (rowBase) format desc order.symm guard
          (n^9000) (n*n^9000) power scan V.scanState A.leafSites

/-- One threshold supplies the exact native cursor handler and its selected
row effects for every nomination and chronological vertex of the fixed pair. -/
theorem eventually_virtualCursorLeafExactCalls (D : FixedProgramDiagonal.Program) (B : S.Templates)
    (u : PairExponents B.growthConstant) (order : B.Entry ≃ Fin g)
    (hg : D.constants.motifLabels = Fintype.card B.Entry) (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      [NeZero (virtualBits D.addressFactor n)] (ht : 21 ≤ 2^(D.geometry n).w) (clk : 44 ≤ n^10000)
      {p : Nat.Primes} {model : LabelEvaluator.Model p (B.compressorDegree n) (B.compressorEquations hn D.constants.circuitExponent)}
      (scalar : D.ScalarData B hn model) (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower))
      (i : D.groupIndices n) (μ : PairStages.Group.Nominations.Nom (D.executionGroup n ht clk))
      (A : CanonicalScan scalar V ξ i (physicalNomination (D := D) (n := n) (ht := ht) (hf := clk) rfl μ))
      (z : (V.selection (M := model)).Choices)
      (m : Memory (D.geometry n).w) (power scan : ℕ), 2 ≤ scan → A.CursorLeafExactCalls order z m power scan := by
  filter_upwards [eventually_ge_atTop 2048, eventually_virtualCursorLeafBounds D B u,
    eventually_selectedRootBudget D B u haddr hnum hden D.constants.circuitExponent,
    eventually_virtualCursorStackBudget D B u haddr hnum hden D.constants.circuitExponent] with n large clocks roots stackBudgets
  intro hn V inst ht clk p model scalar ξ i μ A z m power scan two initial N prepared calendar reference tab bits ord entry later low
  have resources := clocks hn V scalar.advice ξ i μ
  have hf := roots hn V ht clk model.algebra (B.compressorValues hn model) (B.compressorValues_solution hn model)
  have pack := (hf.2.2.2 z).1
  have card : Fintype.card B.Entry = g := (Fintype.card_congr order).trans (Fintype.card_fin g)
  have count := (physical_counter_end (D.executionGroup n ht clk) pack.fit).2.2.trans (hg.trans card)
  have cap := stackBudgets hn V ht clk model.algebra (B.compressorValues hn model) (B.compressorValues_solution hn model) z
  rw [card] at cap
  have arena := V.cursorLeafArena (B.compressorValues hn model) (B.compressorValues_solution hn model)
    z m g pack entry later hf.2.2.1 count cap
  have head := V.cursorLeafHeader scalar.advice ξ i μ prepared pack entry later low
  exact ⟨arena.fit, V.cursorLeafExact scalar ξ i μ order z m resources head arena,
    A.cursorRows order m z power scan large two resources head arena⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
