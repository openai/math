import OAI.Computability.VPVNP.PairVirtualCursorLeafNumbered
import OAI.Computability.VPVNP.PairVirtualCursorLeafHeader
import OAI.Computability.VPVNP.PairVirtualCursorLeafArena
import OAI.Computability.VPVNP.PairVirtualPreparedRoot
import OAI.Computability.VPVNP.PairVertexRoleHandlers
import OAI.Computability.VPVNP.PairVertexSelectedDesc

/-! # Native cursor leaves of the canonical virtual-pair scan -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression
  CompressorRecords
open CursorNetwork CursorBounds VertexImage TreeDecode LocalHistory TraversalRows DFS CutSchedule
  ExponentTrace Filter
open scoped Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 12000

attribute [local irreducible] CursorBounds.wordBits CursorBounds.virtualBits BurstRAM.addressWidth

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
  {D : FixedProgramDiagonal.Program}
    {u : PairExponents B.growthConstant} {n : ℕ} {hn : 2 ≤ n} {p : Nat.Primes}
    {model : LabelEvaluator.Model p (B.compressorDegree n) (B.compressorEquations hn
      D.constants.circuitExponent)}
    {ht : 21 ≤ 2 ^ (D.geometry n).w} {clk : 44 ≤ n ^ 10000}
    [NeZero (virtualBits D.addressFactor n)]
    (V : D.VirtualPairs B u hn D.constants.circuitExponent) (scalar : D.ScalarData B hn model)
    (ξ : Exterior (D.chainHeight n) (n ^ D.constants.deltaPower)) (i : D.groupIndices n)
    (μ : PairStages.Group.Nominations.Nom (D.executionGroup n ht clk))
    {g : ℕ} (order : B.Entry ≃ Fin g)

local notation "group₀" => D.executionGroup n ht clk
local notation "pub" => terminalOperands group₀
local notation "header₀" => vertexHeader group₀
local notation "w₀" => (D.geometry n).w
local notation "dim₀" => virtualBits D.addressFactor n
local notation "lanes₀" => reservedLanes B u n
local notation "baseBits₀" => dim₀ - lanes₀
local notation "X₀" => V.scanState
local notation "T₀" => blockCount (u.θ : ℝ) n
local notation "κ" => B.compressorValues hn model
local notation "ok" => B.compressorValues_solution hn model
local notation "L₀" => BlockProgram.layout B (pub 2).val (X₀).positions T₀
local notation "base₀" => DescriptorSpace.endAddress (L₀)
local notation "seg₀" => TerminalProgram.nativeSegments B D.constants D.numerator D.denominator
  order
local notation "V₀" => VertexImage.placement (seg₀)
local notation "M₀" => PrivateRAM.Template.instantiate (VertexImage.template (seg₀)) w₀ pub
local notation "aux" => V.data scalar.advice ξ i (physicalNomination (D := D) (n := n) (ht := ht)
  (hf := clk) rfl μ)

variable (m : Memory (D.geometry n).w)
local notation "region" => NativeFrame.fromHeader (slotDegree S) pub header₀ m
local notation "offset" => m (header₀ + 14).val
local notation "words" => NativeFrame.leafWords (slotDegree S) pub header₀ offset m

/-- The concrete handler executes the selected nomination with the full
virtual dimension and its actual private fuel. -/
noncomputable abbrev VirtualPairs.cursorLeafParser
    (fit : (region).stackBase + Fintype.card LeafStartup.ScalarPort * n ^ 40 < 2 ^ w₀) :
      HookParser w₀ n :=
  @LeafRole.parser w₀ n words (D.pairLengths i) n (D.geometry n).d (D.geometry n).H
    (n ^ (D.constants.circuitExponent + 5)) (V.layout i) aux dim₀ 0 (roundedUp 1 4 n)
    (inferInstanceAs (NeZero dim₀)) V.cap region fit m (n ^ 39)

variable {V scalar ξ i μ} (A : CanonicalScan scalar V ξ i (physicalNomination (D := D) (n := n)
  (ht := ht) (hf := clk) rfl μ))
    (z : (V.selection (M := model)).Choices) (power scan : ℕ)

local notation "format" => SelectedPacketFormat B κ ok T₀ le_rfl X₀ z (base₀)
local notation "desc" => selectedDesc B κ ok T₀ le_rfl X₀ z (base₀)
local notation "guard" => TerminalLink.workerCell header₀
local notation "histVals" => LeafVisit.cacheWords aux dim₀ (roundedUp 1 4 n)

attribute [local irreducible] BlockSchedule.Templates.execute VertexImage.placement
  VertexImage.template
    CursorNetwork.cursorState NativeOperands.saved NativeOperands.capacity

/-- The initial packets of the mathematical scan execute on the installed
vertex table and use the common cost bound of its shrink and refresh roles. -/
theorem CanonicalScan.cursorRows (large : 2048 ≤ n) (two : 2 ≤ scan)
    (resources : LeafVisit.CursorLeafBounds aux V.cap)
    (head : V.CursorLeafHeader scalar.advice ξ i μ m)
    (arena : V.CursorLeafArena (ht := ht) (clk := clk) κ ok z m g)
    (shrink refresh : HookParser w₀ n) :
    SelectedCursorLeaf.Rows V₀ M₀
      (RoleDomains.handlers (V.cursorLeafParser scalar ξ i μ m arena.fit) shrink refresh)
      m offset region words histVals B.recordLimit (base₀) format desc order.symm guard
      (n ^ 9000) (n * n ^ 9000) power scan X₀ A.leafSites := by
  have shadow (site : BurstRAM.Word (group₀).w) (within : site < LeafRole.addressFields
    (words) .span) :
      TerminalLink.workerCell header₀ (LeafRole.addressFields (words) .shadow + site).val := by
    change site.val < (m (header₀ + 20).val).val at within
    change TerminalLink.workerCell header₀ ((pub 3) + site).val
    have room : (pub 3).val + site.val < 2 ^ (group₀).w :=
      (Nat.add_lt_add_left within (pub 3).val).trans_le head.shadowRoom
    rw [Fin.val_add, Nat.mod_eq_of_lt room]
    exact head.shadowSafe site.val within
  exact SelectedCursorLeaf.numberedRows (S := S) V₀ M₀ aux (Nat.sub_add_cancel V.lanes).symm
    V.dimension V.cap κ A.clock m header₀ offset (slotDegree S) B.recordLimit (base₀)
    (template_contains (seg₀) pub) arena.fit resources large head.stride head.radixB head.radixL
      head.span
    head.shadowRoom head.shadowData arena.size arena.address
    (RoleDomains.handlers (V.cursorLeafParser scalar ξ i μ m arena.fit) shrink refresh) rfl
    guard shadow arena.tag arena.tagRead format desc arena.typed order.symm arena.histWords.ge
    (n ^ 9000) (n * n ^ 9000) power scan two (selectedDesc_leaf B κ ok T₀ le_rfl X₀ z (base₀))

local notation "Y₀" => (V.selection (M := model)).finalState z
local notation "tags₀" => TraversalRoles.selected B κ ok T₀ le_rfl X₀ z

/-- At any chronological site after the packed traversal, the real private
arena is large enough for the handler and its cursor packets have the exact
native effects used by the ordinal computation. -/
def CanonicalScan.CursorLeafCalls : Prop :=
  ∀ {initial : Memory w₀} {N : PairStages.Group.Indexed group₀ Stage.nominations initial
      (PairStages.Group.Nominations.Nom group₀)}
    (prepared : PreparedBranch group₀ initial (physicalPairIndex i)
      ((physicalPairLengths (ht := ht) (hf := clk) i).symm ▸ PairedChain.headers scalar.advice ξ
        i) N μ)
    {calendar reference : Memory w₀} {tab : Fin (L₀).shape.tables} {bits : Fin (Y₀).totalWidth
      → Bool}
    {ord : ℕ},
    TerminalProgram.VertexEntry B κ ok T₀ le_rfl X₀ z (L₀) tab baseBits₀ lanes₀ pub calendar
      reference bits →
    LinkedVertexMemory group₀ reference ord m →
    (∀ x < (pub 2).val, x ≠ (PairTag.address pub).val → calendar x = prepared.copy.memory () x) →
    ∃ fit : (region).stackBase + Fintype.card LeafStartup.ScalarPort * n ^ 40 < 2 ^ w₀,
      ∀ shrink refresh : HookParser w₀ n,
        SelectedCursorLeaf.Rows V₀ M₀
          (RoleDomains.handlers (V.cursorLeafParser scalar ξ i μ m fit) shrink refresh)
          m offset region words histVals B.recordLimit (base₀) format desc order.symm guard
          (n ^ 9000) (n * n ^ 9000) power scan X₀ A.leafSites

/-- One threshold supplies the interpreter, all virtual stacks, the packed
vertex, and every native leaf of every selected occurrence. -/
theorem eventually_virtualCursorLeafCalls (D : FixedProgramDiagonal.Program) (B : S.Templates)
    (u : PairExponents B.growthConstant) (order : B.Entry ≃ Fin g)
    (hg : D.constants.motifLabels = Fintype.card B.Entry) (haddr : max S.laneBits 5 ≤
      D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      [NeZero (virtualBits D.addressFactor n)] (ht : 21 ≤ 2 ^ (D.geometry n).w)
        (clk : 44 ≤ n ^ 10000)
      {p : Nat.Primes} {model : LabelEvaluator.Model p (B.compressorDegree n)
        (B.compressorEquations hn D.constants.circuitExponent)}
      (scalar : D.ScalarData B hn model) (ξ : Exterior (D.chainHeight n)
        (n ^ D.constants.deltaPower))
      (i : D.groupIndices n) (μ : PairStages.Group.Nominations.Nom (D.executionGroup n ht clk))
      (A : CanonicalScan scalar V ξ i (physicalNomination (D := D) (n := n) (ht := ht)
        (hf := clk) rfl μ)) (z : (V.selection (M := model)).Choices)
      (m : Memory (D.geometry n).w) (power scan : ℕ), 2 ≤ scan → A.CursorLeafCalls order m z power
        scan := by
  filter_upwards [eventually_ge_atTop 2048, eventually_virtualCursorLeafBounds D B u,
    eventually_selectedRootBudget D B u haddr hnum hden D.constants.circuitExponent,
    eventually_virtualCursorStackBudget D B u haddr hnum hden D.constants.circuitExponent]
      with n large clocks roots stackBudgets
  intro hn V nz ht clk p model scalar ξ i μ A z m power scan two initial N prepared calendar
    reference tab bits ord entry later low
  have hf := roots hn V ht clk model.algebra (B.compressorValues hn model)
    (B.compressorValues_solution hn model)
  have pack := (hf.2.2.2 z).1
  have card : Fintype.card B.Entry = g := (Fintype.card_congr order).trans (Fintype.card_fin g)
  have count := (physical_counter_end (D.executionGroup n ht clk) pack.fit).2.2.trans
    (hg.trans card)
  have cap := stackBudgets hn V ht clk model.algebra (B.compressorValues hn model)
    (B.compressorValues_solution hn model) z
  rw [card] at cap
  have arena := V.cursorLeafArena (B.compressorValues hn model) (B.compressorValues_solution hn
    model)
    z m g pack entry later hf.2.2.1 count cap
  have head := V.cursorLeafHeader scalar.advice ξ i μ prepared pack entry later low
  refine ⟨arena.fit, fun shrink refresh => ?_⟩
  exact A.cursorRows order m z power scan large two (clocks hn V scalar.advice ξ i μ) head arena
    shrink refresh

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
