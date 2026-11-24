import OAI.Computability.VPVNP.PairVirtualPreparedRoot
import OAI.Computability.VPVNP.PairVertexRatedClock
import OAI.Computability.VPVNP.PairVertexRatedRoot
import OAI.Computability.VPVNP.PairVertexSelectedDesc
import OAI.Computability.VPVNP.PairVertexSelectedRoles

/-! # Measured ordinal calls of the installed pair program -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression
open CompressorRecords DescriptorSpace CursorNetwork CursorBounds Filter LocalHistory TraversalRows
open VertexImage CutSchedule ExponentTrace TreeDecode TraversalRoles
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {D : FixedProgramDiagonal.Program}
  {B : S.Templates} {u : PairExponents B.growthConstant}
  {n : ℕ} {hn : 2 ≤ n} {ht : 21 ≤ 2^(D.geometry n).w} {clk : 44 ≤ n^10000}
  (V : D.VirtualPairs B u hn D.constants.circuitExponent)
  (adv : Bits (n^D.constants.advicePower)) (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower))
  (i : D.groupIndices n) (μ : PairStages.Group.Nominations.Nom (D.executionGroup n ht clk))
  {labels : ℕ} (order : B.Entry ≃ Fin labels)

local notation "G₀" => D.executionGroup n ht clk
local notation "pub" => terminalOperands G₀
local notation "hdr" => vertexHeader G₀
local notation "degree" => slotDegree S
local notation "T₀" => blockCount (u.θ : ℝ) n
local notation "X₀" => V.scanState
local notation "S₀" => TerminalProgram.nativeSegments B D.constants D.numerator D.denominator order
local notation "V₀" => VertexImage.placement S₀
local notation "M₀" => PrivateRAM.Template.instantiate (VertexImage.template S₀) (Geometry.w (D.geometry n)) pub
local notation "aux" => V.data adv ξ i (physicalNomination rfl μ)
local notation "W₀" => Geometry.w (D.geometry n)
local notation "vals₀" => LeafVisit.cacheWords aux (virtualBits D.addressFactor n) (roundedUp 1 4 n)

attribute [local irreducible] BlockSchedule.Templates.execute BlockProgram.layout VertexImage.template
  VertexImage.placement CursorNetwork.cursorState CursorBounds.wordBits NativeOperands.capacity NativeOperands.saved

/-- The local role contracts on one selected physical memory. Every
packet type and address comes from this same execution. -/
def VirtualPairs.SelectedRowsAt {A : Type*} [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f)
    (P : SiteParsers f (X₀).network) (z : (B.execute f ok T₀ le_rfl X₀).Choices)
    (m : Memory W₀) (power scan : ℕ) : Prop :=
  let rowBase := endAddress (BlockProgram.layout B (pub 2).val (X₀).positions T₀)
  let R := NativeFrame.fromHeader degree pub hdr m
  let role := m (hdr+14).val
  let data := NativeFrame.leafWords degree pub hdr role m
  let format := SelectedPacketFormat B f ok T₀ le_rfl X₀ z rowBase
  let desc := selectedDesc B f ok T₀ le_rfl X₀ z rowBase
  let valid : List NodeArguments.Packet → DFS.Scratch W₀ (pub 6).val → Prop := Budgeted R.arguments format (VertexFrameData R data role vals₀) desc
    (privateHistogram order.symm R.histBase) (n^9000) ((pub 6).val*n^9000)
  ∃ domain handlers, SelectedChecks B f ok T₀ le_rfl X₀ z rowBase V₀ M₀ m
    ((NativeFrame.frameBase R : ℕ) : BurstRAM.Word W₀) role R.histBase order.symm P valid domain handlers
    (ordinalJobCost n power scan)

/-- The calendar boundary, published traversal rows and complete shared
bit scan feed every subsequent active ordinal on the linked memory. -/
def VirtualPairs.RatedAtBoundary {A : Type*} [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f)
    (P : SiteParsers f (X₀).network) (z : (B.execute f ok T₀ le_rfl X₀).Choices)
    (baseBits laneBits initialWidth inputN power scan : ℕ) (online calendar reference m : Memory W₀) : Prop :=
  let X := X₀
  let E := B.execute f ok T₀ le_rfl X
  let Y := E.finalState z
  let L := BlockProgram.layout B (pub 2).val X.positions T₀
  let tab : Fin L.shape.tables := ⟨0, by unfold L BlockProgram.layout; change 0 < 6; decide⟩
  let saved := CursorRAM.ScheduleInit.inputs (CursorRAM.encode W₀ (directoryBase L))
    (CursorRAM.encode W₀ 1) baseBits laneBits (S.degreeExponent 0) initialWidth (incidenceStart L 0)
  let resident := CurrentResident.resident B f ok ⟨leafLayer (siteOrder X),.cursor⟩ L (endAddress L) inputN saved
  ScheduledTrace.Boundary resident pub (levelWords L : BurstRAM.Word W₀) (directoryRows L) (directoryRows L)
      (executeLevels B f ok T₀ le_rfl X z) Y online →
    SourceTransport.Agree ((pub 2).val+6 ≤ ·) online calendar →
    ∀ bits : Fin Y.totalWidth → Bool,
      TerminalProgram.VertexEntry B f ok T₀ le_rfl X z L tab baseBits laneBits pub calendar reference bits →
      ∀ j : Fin (siteOrder Y).length, LinkedVertexMemory G₀ reference j.val m →
      V.SelectedRowsAt adv ξ i μ order f ok P z m power scan →
      let half := TerminalGatherGeometry.half Y (fun p => bits (Fin.cast (TerminalPrefix.width_sum Y) p))
      ∀ cap, n^9999 ≤ cap → Nonempty (RatedOrdinal B f ok T₀ le_rfl X z (endAddress L) V₀ M₀
        (pub 4).val (pub 5).val order.symm P half cap m j n power scan)

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 10000 in
/-- The threshold precedes the virtual layout, exterior assignment,
nomination, coefficient realization, selected compression and bit scan. -/
theorem eventually_rated_at_boundary (D : FixedProgramDiagonal.Program) (B : S.Templates)
    (u : PairExponents B.growthConstant) (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den)
    (hlabels : D.constants.motifLabels = Fintype.card B.Entry) {labels : ℕ} (order : B.Entry ≃ Fin labels) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      (ht : 21 ≤ 2^(D.geometry n).w) (clk : 44 ≤ n^10000)
      (adv : Bits (n^D.constants.advicePower)) (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower))
      (i : D.groupIndices n) (μ : PairStages.Group.Nominations.Nom (D.executionGroup n ht clk))
      (A : Type*) [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f) (P : SiteParsers f V.scanState.network)
      (z : (B.execute f ok (blockCount (u.θ : ℝ) n) le_rfl V.scanState).Choices)
      (baseBits laneBits initialWidth inputN power scan : ℕ) (online calendar reference m : Memory (D.geometry n).w),
      V.RatedAtBoundary adv ξ i μ order f ok P z baseBits laneBits initialWidth inputN power scan online calendar reference m := by
  filter_upwards [eventually_selectedRootBudget D B u haddr hnum hden D.constants.circuitExponent,
    eventually_rated_root_clock D B u haddr D.constants.circuitExponent] with n budget clocks
  intro hn V ht clk adv ξ i μ A _ f ok P z baseBits laneBits initialWidth inputN power scan online calendar reference m
  let G := D.executionGroup n ht clk
  let ops := terminalOperands G
  let H := vertexHeader G
  let T := blockCount (u.θ : ℝ) n
  let X := V.scanState
  let E := B.execute f ok T le_rfl X
  let Y := E.finalState z
  let L := BlockProgram.layout B (ops 2).val X.positions T
  let ls := selectedLayers B f ok T le_rfl X z
  let tags := TraversalRoles.selected B f ok T le_rfl X z
  let parts := TerminalProgram.nativeSegments B D.constants D.numerator D.denominator order
  let host := (VertexImage.template parts).instantiate (D.geometry n).w ops
  have card : labels = Fintype.card B.Entry := (Fintype.card_fin labels).symm.trans (Fintype.card_congr order.symm)
  obtain ⟨large,geometry,length,branches⟩ := budget hn V ht clk A f ok
  obtain ⟨fit,width,stack⟩ := branches z
  obtain ⟨capacity,weights⟩ := clocks.2.2.2.2 hn V A f ok
  have actual := V.root_at_boundary adv ξ i μ order f ok z baseBits laneBits initialWidth inputN
    online calendar reference m hlabels large geometry length fit width stack
  unfold VirtualPairs.RatedAtBoundary
  intro _ _ _ _ tab saved resident boundary handoff bits entry j later checks half cap room
  obtain ⟨domain,handlers,checked⟩ := checks
  let v := (siteOrder Y).entries j
  have run := actual boundary handoff bits entry j later
  have wordsEq : tagWords B.recordLimit tags = words B.recordLimit ls :=
    congrArg (words B.recordLimit) (selected_layers B f ok T le_rfl X z)
  have arena := fit.arena
  rw [wordsEq] at arena
  change endAddress L + 2*words B.recordLimit ls + Y.totalWidth ≤ H.val at arena
  have headerFit : H.val+32 ≤ 2^(D.geometry n).w := fit.room
  have tightHeader : H.val+31 < 2^(D.geometry n).w := by omega
  have rowBounds : endAddress L+words B.recordLimit ls ≤ H.val := by omega
  have selectedRows : AllRows (D.geometry n).w m B.recordLimit (endAddress L) (endAddress L) ls := by
    have layerEq : tags.map TaggedLayer.layer = ls := selected_layers B f ok T le_rfl X z
    rw [← layerEq]
    apply fit.rows later
    · rw [layerEq]; exact selected_capacity B f ok T le_rfl X z
    · rw [layerEq]; exact entry.rows
  have labelCount : (ops 9).val = Fintype.card B.Entry := (physical_counter_end G fit.fit).2.2.trans hlabels
  have regions := entry.selected_regions fit later n (Fintype.card B.Entry) length labelCount
  have cache : (NativeFrame.fromHeader (slotDegree S) ops H m).cacheBase+38 ≤ 2^(D.geometry n).w := by
    rw [regions]; exact stack.le
  have ext : (ops 4).val + (ops 5).val + labels ≤ H.val := by
    have counter := fit.counter_rows
    change (ops 4).val + (ops 5).val + D.constants.motifLabels ≤ endAddress L at counter
    rw [hlabels,←card] at counter
    omega
  let format := SelectedPacketFormat B f ok T le_rfl X z (endAddress L)
  let desc := selectedDesc B f ok T le_rfl X z (endAddress L)
  apply RootRun.ratedOrdinal B f ok T le_rfl X z (endAddress L) (VertexImage.placement parts)
    host m (ops 4).val (ops 5).val order.symm P half cap j (slotDegree S) _ n power scan (n^9000)
    _ format desc domain handlers run checked (selected_root_format B f ok T le_rfl X z _ v _)
    (selectedDesc_root B f ok T le_rfl X z _ v _) selectedRows rowBounds tightHeader cache
    (capacity.trans_eq length.symm) ext (Fin.cast_val_eq_self _).symm (Fin.cast_val_eq_self _).symm
    ((Fin.cast_val_eq_self _).symm.trans (congrArg (fun x : ℕ => (x : BurstRAM.Word (D.geometry n).w)) (labelCount.trans card.symm)))
    clocks.2.2.2.1
  intro t ht'
  have tick := (weights z).2 v |>.2 (half v) t ht'
  rw [← card] at tick
  exact tick.trans room

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
