import OAI.Computability.VPVNP.PairVirtualRootBudget
import OAI.Computability.VPVNP.PairVertexRootEntry
import OAI.Computability.VPVNP.PairSelectedPacketGeometry
import OAI.Computability.VPVNP.PairSimulationLeafRoleHandler
import OAI.Computability.VPVNP.PairTerminalFootprint

/-!
# Cursor rows in the live virtual pair arena

The shared-bit handoff publishes the first row and the role displacement.
Earlier ordinals preserve both fields and the selected role table, so every
cursor read uses the original row address and stays below the terminal header.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

section

open BurstRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression
open CompressorRecords DescriptorSpace CursorNetwork CursorBounds Filter TraversalRows

variable {K : Type*} [_root_.Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program)
  (B : S.Templates) (u : PairExponents B.growthConstant)

attribute [local irreducible] BlockSchedule.Templates.execute BlockProgram.layout
  CursorNetwork.cursorState

/-- All private cursor stacks for a selected virtual branch fit at one input-length threshold. -/
theorem eventually_virtualCursorStackBudget (haddr : max S.laneBits 5 ≤ D.addressFactor)
    (hnum : D.numerator = (liveRatio u).num) (hden : D.denominator = (liveRatio u).den) (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn C) (ht : 21 ≤ 2 ^ (D.geometry n).w)
      (clk : 44 ≤ n ^ 10000) (A : Type*) [CommRing A] (f : B.Entry → A) (ok : B.IsSolution f),
      let X := V.scanState
      let T := blockCount (u.θ : ℝ) n
      let E := B.execute f ok T le_rfl X
      let pub := terminalOperands (D.executionGroup n ht clk)
      let L := BlockProgram.layout B (pub 2).val X.positions T
      ∀ z : E.Choices,
        let rows := words B.recordLimit (selectedLayers B f ok T le_rfl X z)
        (TerminalLayout.privateRegions (slotDegree S) n (endAddress L + rows)
          (Fintype.card B.Entry)).stackBase +
          Fintype.card LeafStartup.ScalarPort * n ^ 40 < 2 ^ (D.geometry n).w := by
  let start := fun n => (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
  have poly : PolynomiallyBounded start := by
    have eqn : start = fun n => (LiveProgram.Layout.pairWorkspace D.constants).eval
        (paperGeometry D.addressFactor (liveCapacity u) n) := by
      funext n
      change (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n) = _
      rw [paperGeometry_eq D B u hnum hden n]
    rw [eqn]
    exact CompressedPair.startup_workspace_polynomial _ D.address_pos (liveCapacity_polynomial u)
  filter_upwards [CompressedPair.eventually_startup_inputs D.constants D.address_pos
    (liveCapacity_polynomial u),
    TerminalLayout.eventually_packedFit B u D.addressFactor haddr poly
      (Fintype.card LeafStartup.ScalarPort) (fun _ => 0) (PolynomiallyBounded.const 0)]
    with n hwords hstack
  intro hn V ht clk A inst f ok
  dsimp only
  rw [V.scanState_pairInput]
  let G := D.executionGroup n ht clk
  let coords := laneLabels _ _ V.lanes
  have pub := hwords (CounterPublic.actualPrefix D.literal)
  rw [← paperGeometry_eq D B u hnum hden n] at pub
  have workspace : (terminalOperands G 2).val = start n := pub.1
  intro z
  have bound := (hstack coords V.dimension le_rfl A f ok z).2.2.2.1
  change (TerminalLayout.privateRegions _ _
    (endAddress (BlockProgram.layout B (terminalOperands G 2).val _ _) + _) _).stackBase + _ < _
  rw [workspace, pairInput_positions]
  simp only [Nat.add_zero] at bound
  exact bound

end

open BurstRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression CompressorRecords
open DescriptorSpace CursorNetwork LocalHistory TraversalRows TraversalRoles TreeDecode
open scoped Fin.CommRing

variable {K A : Type*} [_root_.Field K] [CommRing A] {S : BlockSchedule K}
  {B : S.Templates} {u : PairExponents B.growthConstant} {D : FixedProgramDiagonal.Program}
  {n C : ℕ} {hn : 2 ≤ n} {ht : 21 ≤ 2 ^ (D.geometry n).w} {clk : 44 ≤ n ^ 10000}
  (V : D.VirtualPairs B u hn C) (f : B.Entry → A) (ok : B.IsSolution f)

local notation "G₀" => D.executionGroup n ht clk
local notation "pub" => terminalOperands G₀
local notation "hdr" => vertexHeader G₀
local notation "w₀" => Geometry.w (D.geometry n)
local notation "T₀" => blockCount (u.θ : ℝ) n
local notation "X₀" => V.scanState
local notation "L₀" => BlockProgram.layout B (Fin.val (pub 2)) (State.positions X₀) T₀
local notation "first₀" => endAddress (L₀)
local notation "leaves₀" => sitePointers B.recordLimit (first₀) (siteOrder X₀)

variable (z : (B.execute f ok (blockCount (u.θ : ℝ) n) le_rfl V.scanState).Choices)
  (m : Memory (D.geometry n).w)

local notation "Y₀" => StateExecution.finalState (B.execute f ok T₀ le_rfl X₀) z
local notation "layers₀" => selectedLayers B f ok T₀ le_rfl X₀ z
local notation "rows₀" => words B.recordLimit (layers₀)
local notation "tags₀" => selected B f ok T₀ le_rfl X₀ z
local notation "R₀" => NativeFrame.fromHeader (slotDegree S) pub hdr m
local notation "offset₀" => m (Fin.val (hdr + 14))
local notation "data₀" => NativeFrame.leafWords (slotDegree S) pub hdr (offset₀) m

attribute [local irreducible] BlockSchedule.Templates.execute BlockProgram.layout
  CursorNetwork.cursorState CursorBounds.wordBits CursorBounds.virtualBits

/-- The actual public cursor tags and private arena used at an ordinal. -/
structure VirtualPairs.CursorLeafArena (labels : ℕ) : Prop where
  fit : (R₀).stackBase + Fintype.card LeafStartup.ScalarPort * n ^ 40 < 2 ^ w₀
  size : (pub 6).val = n
  address : (first₀) = (LeafRole.addressFields (data₀) .base).val
  nodes : (R₀).nodes = (first₀) + (rows₀)
  histWords : (R₀).histWords = labels
  typed : ∀ q, SelectedPacketFormat B f ok T₀ le_rfl X₀ z (first₀) q →
    q.node < (R₀).nodes ∧ q.node < 2 ^ w₀
  tag : ∀ u, m ((offset₀) + (((leaves₀) u).1 : Word w₀)).val = 0
  tagRead : ∀ u, TerminalLink.workerCell hdr ((offset₀) + (((leaves₀) u).1 : Word w₀)).val

open private ptr_bounds from OAI.Computability.VPVNP.PairTraversalDisjoint

/-- The packed descriptor interval, surviving header publications and the
allocated scalar stacks supply every cursor address and tag bound. -/
theorem VirtualPairs.cursorLeafArena (labels : ℕ)
    {tab : Fin (L₀).shape.tables} {baseBits laneBits ord : ℕ}
    {calendar reference : Memory w₀} {bits : Fin (Y₀).totalWidth → Bool}
    (pack : VertexPacked G₀ (L₀) B.recordLimit (tags₀) (Y₀).totalWidth)
    (entry : TerminalProgram.VertexEntry B f ok T₀ le_rfl X₀ z (L₀) tab baseBits laneBits
      pub calendar reference bits)
    (later : LinkedVertexMemory G₀ reference ord m)
    (length : (pub 6).val = n) (count : (pub 9).val = labels)
    (stack : (TerminalLayout.privateRegions (slotDegree S) n ((first₀) + (rows₀)) labels).stackBase
      + Fintype.card LeafStartup.ScalarPort * n ^ 40 < 2 ^ w₀) :
    V.CursorLeafArena (ht := ht) (clk := clk) f ok z m labels := by
  have sizeEq : tagWords B.recordLimit (tags₀) = (rows₀) :=
    congrArg (words B.recordLimit) (selected_layers B f ok T₀ le_rfl X₀ z)
  have arena := pack.arena
  rw [sizeEq] at arena
  have room : (hdr).val + 32 ≤ 2 ^ w₀ := pack.room
  have headRoom : (hdr).val + 31 < 2 ^ w₀ := by omega
  have reg := entry.selected_regions pack later n labels length count
  have firstField := entry.packedField pack 4 (by decide) (by decide) (by decide)
  change reference (hdr + 4).val = ((first₀) : Word w₀) at firstField
  have rowField : m (hdr + 4).val = ((first₀) : Word w₀) :=
    (pack.header later 4 (by decide) (by decide)).trans firstField
  have displacement : (offset₀).val = (rows₀) + (Y₀).totalWidth := by
    have phys := pack.header later 14 (by decide) (by decide)
    change m (hdr + 14).val = reference (hdr + 14).val at phys
    have field : (hdr + 14).val = (hdr).val + 14 :=
      TerminalFootprint.header_val hdr headRoom (j := 14) (by decide)
    rw [phys, field,
      entry.offset, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have tags := pack.roleWords later (sizeEq ▸ entry.roles)
  have cursor (u : (X₀).network.Site) :
      m ((offset₀) + (((leaves₀) u).1 : Word w₀)).val = 0 ∧
        TerminalLink.workerCell hdr ((offset₀) + (((leaves₀) u).1 : Word w₀)).val := by
    have leafEnd : address B.recordLimit (first₀) (siteOrder X₀).length ≤ (first₀) + (rows₀) := by
      rw [selectedLayers_eq_levels B f ok T₀ le_rfl X₀ z]
      simp only [address, words, List.map_cons, leafLayer, List.sum_cons, Nat.mul_add]
      exact Nat.add_le_add_left (Nat.le_add_right _ _) _
    have row := (ptr_bounds (siteOrder X₀) B.recordLimit (first₀) u).2.trans_le leafEnd
    have below : (offset₀).val + ((leaves₀) u).1 < (hdr).val := by omega
    have atTag : ((offset₀) + (((leaves₀) u).1 : Word w₀)).val =
        (offset₀).val + ((leaves₀) u).1 := by
      rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : ((leaves₀) u).1 < 2 ^ w₀),
        Nat.mod_eq_of_lt (by omega)]
    rw [atTag]
    refine ⟨?_, TerminalFootprint.below hdr headRoom below⟩
    rw [displacement]
    exact reads_cursor B f ok T₀ le_rfl X₀ z m _ _ (sizeEq ▸ tags) u
  refine ⟨reg ▸ stack, length, ?_, congrArg LeafArena.Regions.nodes reg,
    congrArg LeafArena.Regions.histWords reg, ?_, fun u => (cursor u).1, fun u => (cursor u).2⟩
  · change (first₀) = (m (hdr + 4).val).val
    rw [rowField, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  · intro q hq
    have h := selected_packet_node B f ok T₀ le_rfl X₀ z (first₀) hq
    exact ⟨reg ▸ h, by omega⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
