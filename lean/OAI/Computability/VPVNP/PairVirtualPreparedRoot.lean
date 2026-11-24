import OAI.Computability.VPVNP.PairVirtualRootBudget
import OAI.Computability.VPVNP.PairVirtualVertexRoot
import OAI.Computability.VPVNP.PairVertexRootEntry
import OAI.Computability.VPVNP.PairVertexRootEntryRows

/-!
# The selected calendar reaches its actual native root

Every ordinal in the physical shared-bit post-memory enters the selected
root row. Its cache uses the real nomination. The private argument is the
two half-wire lists in the same site and edge order as the compressed path.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression
open CompressorRecords DescriptorSpace CursorNetwork CursorBounds Filter LocalHistory TraversalRows
open VertexImage CutSchedule ExponentTrace
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
local notation "M₀" => PrivateRAM.Template.instantiate (VertexImage.template S₀) (Geometry.w (D.geometry n)) pub
local notation "aux" => V.data adv ξ i (physicalNomination rfl μ)
local notation "W₀" => Geometry.w (D.geometry n)

attribute [local irreducible] BlockSchedule.Templates.execute BlockProgram.layout VertexImage.template
  VertexImage.placement CursorNetwork.cursorState CursorBounds.wordBits NativeOperands.capacity NativeOperands.saved

/-- The native root result on an actual online boundary, its terminal handoff and the
shared-bit memory. All active ordinals use the same selected table image. -/
def VirtualPairs.SelectedRootCalls {A : Type*} [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f)
    (z : (B.execute f ok T₀ le_rfl X₀).Choices) (baseBits laneBits initialWidth inputN : ℕ)
    (online calendar reference m : Memory W₀) : Prop :=
    let X := X₀
    let T := T₀
    let E := B.execute f ok T le_rfl X
    let Y := E.finalState z
    let L := BlockProgram.layout B (pub 2).val X.positions T
    let tab : Fin L.shape.tables := ⟨0, by unfold L BlockProgram.layout; change 0 < 6; decide⟩
    let saved := CursorRAM.ScheduleInit.inputs (CursorRAM.encode W₀ (directoryBase L))
      (CursorRAM.encode W₀ 1) baseBits laneBits (S.degreeExponent 0) initialWidth (incidenceStart L 0)
    let resident := CurrentResident.resident B f ok ⟨leafLayer (siteOrder X),.cursor⟩ L (endAddress L) inputN saved
    ScheduledTrace.Boundary resident pub (levelWords L : BurstRAM.Word W₀) (directoryRows L) (directoryRows L)
      (executeLevels B f ok T le_rfl X z) Y online →
    SourceTransport.Agree ((pub 2).val+6 ≤ ·) online calendar →
    ∀ bits : Fin Y.totalWidth → Bool,
      TerminalProgram.VertexEntry B f ok T le_rfl X z L tab baseBits laneBits pub calendar reference bits →
      ∀ j : Fin (siteOrder Y).length, LinkedVertexMemory G₀ reference j.val m →
      let v := (siteOrder Y).entries j
      let bitData := fun p => bits (Fin.cast (TerminalPrefix.width_sum Y) p)
      let packet : NodeArguments.Packet := ⟨(selectedTrees B f ok T le_rfl X z (endAddress L) v).address,
        NodeArguments.packed Y v (TerminalGatherGeometry.half Y bitData v)⟩
      VertexImage.RootRun (VertexImage.placement S₀) M₀ m (j.val : BurstRAM.Word W₀) degree (S.degreeExponent 0)
        (NativeOperands.work (NativeCache.args D.constants) D.numerator D.denominator (D.geometry n)+76)
        packet (LeafVisit.cacheWords aux (CursorBounds.virtualBits D.addressFactor n) (roundedUp 1 4 n))

/-- One real selected site, from the online boundary and physical shared-bit
entry. The retained private packet names the actual selected tree root. -/
theorem VirtualPairs.root_at_boundary {A : Type*} [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f)
    (z : (B.execute f ok T₀ le_rfl X₀).Choices) (baseBits laneBits initialWidth inputN : ℕ)
    (online calendar reference m : Memory W₀) (hg : D.constants.motifLabels = Fintype.card B.Entry)
    (large : 3 ≤ n) (fit : PairNativeGeometry.Fits D.numerator D.denominator n W₀)
    (length : (pub 6).val = n) :
    let X := X₀
    let T := T₀
    let E := B.execute f ok T le_rfl X
    let Y := E.finalState z
    let L := BlockProgram.layout B (pub 2).val X.positions T
    let ls := selectedLayers B f ok T le_rfl X z
    let tags := TraversalRoles.selected B f ok T le_rfl X z
    VertexPacked G₀ L B.recordLimit tags Y.totalWidth → Y.maxWireWidth ≤ n →
    (TerminalLayout.privateRegions degree n (endAddress L+words B.recordLimit ls) (Fintype.card B.Entry)).stackBase < 2^W₀ →
    V.SelectedRootCalls adv ξ i μ order f ok z baseBits laneBits initialWidth inputN online calendar reference m := by
  intro X T E Y L ls tags P width stack
  unfold VirtualPairs.SelectedRootCalls
  intro _ _ _ _ _ tab saved resident boundary handoff bits entry j later v bitData packet
  have ⟨slots,cells⟩ := selected_table_capacity B f ok T le_rfl X z (pub 2).val
  have levelFit : ls.dropLast.length < L.levels := by
    rw [show ls.dropLast.length = T*(S.steps+1) from TerminalBootstrap.selected_prior_length ..,
      show L.levels = 1+(S.steps+1)*T from BlockProgram.actual_level_count ..,Nat.mul_comm T]
    omega
  let last : Fin L.levels := ⟨ls.dropLast.length,levelFit⟩
  have arena := P.arena
  have room := P.room
  have endFit : endAddress L < 2^W₀ := by change (hdr).val+32 ≤ 2^W₀ at room; omega
  have cols := (TerminalPrefix.Linked.boundary_inputs B f ok T le_rfl X z X.positions baseBits laneBits initialWidth inputN
    pub online calendar boundary handoff endFit slots).2.2
  let state : BurstRAM.Word W₀ := (j.val : BurstRAM.Word W₀)
  have rows := entry.gather_rows degree state levelFit endFit slots (by
    change (hdr).val+12 ≤ 2^W₀; change (hdr).val+32 ≤ 2^W₀ at room; omega) cols
  have jFit : j.val < 2^W₀ := by
    have h := (P.heads last tab _ slots cells (DescriptorSpace.tableBase L last tab) (by simp)).2
    have count : (siteOrder Y).length ≤ TerminalPrefix.arcCount Y :=
      Nat.le_mul_of_pos_right _ (Nat.two_pow_pos (S.degreeExponent 0))
    exact j.isLt.trans_le (count.trans ((Nat.le_add_left ..).trans (h.trans endFit.le)))
  have index : state.val = ((siteOrder Y).entries.symm v).val := by
    change j.val % (2^W₀) = ((siteOrder Y).entries.symm ((siteOrder Y).entries j)).val
    rw [Nat.mod_eq_of_lt jFit,Equiv.symm_apply_apply]
  have labelCount : (pub 9).val = Fintype.card B.Entry := (physical_counter_end G₀ P.fit).2.2.trans hg
  have inputs := entry.rootInputs P later n (Fintype.card B.Entry) length labelCount width stack
    v state index last rfl slots cells rows
  have run := V.active_root adv ξ i μ order Y v m state bitData inputs large fit
  have sizeEq : TraversalRoles.tagWords B.recordLimit tags = words B.recordLimit ls :=
    congrArg (words B.recordLimit) (TraversalRoles.selected_layers B f ok T le_rfl X z)
  rw [sizeEq] at arena
  have rowFit : endAddress L + words B.recordLimit ls ≤ 2^W₀ := by
    change (hdr).val+32 ≤ 2^W₀ at room
    omega
  have root := entry.gather_root v degree state index room rowFit
  have same := P.gatherLayout later degree state
  have eqPacket : VertexRootPacket.packet Y (TerminalRootGather.Layout.ofHeader degree pub hdr state m) v bitData = packet := by
    rw [same]
    exact congrArg (fun k => NodeArguments.Packet.mk k (NodeArguments.packed Y v (TerminalGatherGeometry.half Y bitData v))) root.symm
  rw [eqPacket] at run
  exact run


/-- The auxiliary shadow and every selected root on the same physical
nomination, uniformly in the scalar assignment and all selected choices. -/
theorem eventually_preparedRoots (D : FixedProgramDiagonal.Program) (B : S.Templates)
    (u : PairExponents B.growthConstant) (order : B.Entry ≃ Fin labels)
    (hg : D.constants.motifLabels = Fintype.card B.Entry) (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn D.constants.circuitExponent)
      (ht : 21 ≤ 2^(D.geometry n).w) (clk : 44 ≤ n^10000) (adv : Bits (n^D.constants.advicePower))
      (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)) (i : D.groupIndices n),
      let G := D.executionGroup n ht clk
      ∀ (μ : PairStages.Group.Nominations.Nom G) {initial : Memory G.w}
        {N : PairStages.Group.Indexed G Stage.nominations initial (PairStages.Group.Nominations.Nom G)}
        (P : PreparedBranch G initial (physicalPairIndex i)
          ((physicalPairLengths (ht := ht) (hf := clk) i).symm ▸ PairedChain.headers adv ξ i) N μ)
        (A : Type*) [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f),
        (∀ x, P.copy.memory () ((shadow G).val+x) = (V.data adv ξ i (physicalNomination rfl μ)).initial x) ∧
        ∀ (z : (B.execute f ok (blockCount (u.θ : ℝ) n) le_rfl V.scanState).Choices)
          (baseBits laneBits initialWidth inputN : ℕ) (online calendar reference m : Memory G.w),
          V.SelectedRootCalls adv ξ i μ order f ok z baseBits laneBits initialWidth inputN online calendar reference m := by
  filter_upwards [eventually_selectedRootBudget D B u haddr hnum hden D.constants.circuitExponent]
    with n ready hn V ht clk adv ξ i G μ initial N P A inst f ok
  have ⟨large,fit,length,branches⟩ := ready hn V ht clk A f ok
  refine ⟨V.shadow_initial rfl adv ξ i μ P,?_⟩
  intro z baseBits laneBits initialWidth inputN online calendar reference m
  have ⟨packed,width,stack⟩ := branches z
  exact V.root_at_boundary adv ξ i μ order f ok z baseBits laneBits initialWidth inputN online calendar reference m
    hg large fit length packed width stack

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
