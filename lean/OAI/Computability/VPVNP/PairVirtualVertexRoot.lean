import OAI.Computability.VPVNP.PairVertexRootInputs
import OAI.Computability.VPVNP.PairTerminalVertexFramePacked
import OAI.Computability.VPVNP.PairVertexActiveRoot
import OAI.Computability.VPVNP.PairVertexAscendingPaths
import OAI.Computability.VPVNP.PairTerminalNativeTable
import OAI.Computability.VPVNP.LiveVirtualPairReadback

/-!
# The actual virtual counter at the native terminal root

The eleven words and the code at the site entry belong to the fixed live
group. The primed machine initialized by the cache is the same one selected
for the exterior assignment, pair index and nomination.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM LiveProgram Compression CompressorRecords.SourceTransport
open scoped Fin.CommRing

/-- A bounded execution from the vertex entry to the active root state. Its event trace has the
prescribed length and probe count, reads the worker header cell, consumes no choice bits
and restores the incoming memory. -/
structure RootRun {S : Part → Segment} {w p r : ℕ} (A : Placement S p r) (M : Machine w p r 11)
    (m : Memory w) (ordinal : Word w) (degree exponent bound : ℕ) (packet : NodeArguments.Packet)
    (vals : LeafSourceLoad.Static 34 → Word w) : Prop where
  run : ∃ t ≤ bound, ∃ out : Config w p r, ∃ es : List (Event w),
    ActiveRootState A out ordinal (M.publicData 6) (m (TerminalLink.header M.publicData+14).val)
      (NativeFrame.fromHeader degree M.publicData (TerminalLink.header M.publicData) m) packet
      (NativeFrame.leafWords degree M.publicData (TerminalLink.header M.publicData)
        (m (TerminalLink.header M.publicData+14).val) m)
      (NativeFrame.fields degree M.publicData (TerminalLink.header M.publicData)
        (m (TerminalLink.header M.publicData+14).val) m) vals ∧
    es.length = t+degree+187+(15+21*(2^exponent)+5*packet.bits.length) ∧
    countProbes es = 15+(5*(2^exponent)+packet.bits.length) ∧ choiceBits es = [] ∧ after m es = m ∧
    Reads (TerminalLink.workerCell (TerminalLink.header M.publicData)) es ∧
    TerminalRootGather.Prefix M m (M.program.start ordinal) es out

end PairSimulation.VertexImage

namespace FixedProgramDiagonal.Program

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary PairSimulation Compression CompressorRecords
open CursorNetwork VertexImage CutSchedule ExponentTrace Filter
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
  {u : PairExponents B.growthConstant} {D : FixedProgramDiagonal.Program} {n : ℕ}
  {hn : 2 ≤ n} (V : D.VirtualPairs B u hn D.constants.circuitExponent)
  {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000}
  (adv : Bits (n^D.constants.advicePower)) (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower))
  (i : D.groupIndices n) (μ : PairStages.Group.Nominations.Nom (D.executionGroup n ht hf))
  {labels : ℕ} (order : B.Entry ≃ Fin labels)

local notation "G₀" => D.executionGroup n ht hf
local notation "S₀" => TerminalProgram.nativeSegments B D.constants D.numerator D.denominator order
local notation "A₀" => VertexImage.placement S₀
local notation "pub" => terminalOperands G₀
local notation "hdr" => vertexHeader G₀
local notation "M₀" => PrivateRAM.Template.instantiate (VertexImage.template S₀) (Geometry.w (D.geometry n)) pub
local notation "degree" => slotDegree S
local notation "aux" => V.data adv ξ i (physicalNomination rfl μ)

attribute [local irreducible] VertexImage.placement VertexImage.template NativeOperands.capacity
  NativeOperands.saved VertexGeometry.segment CursorBounds.wordBits CursorBounds.virtualBits
  TerminalRootGather.segment

/-- Execute the concrete arithmetic, cache and root gather for the chosen
physical nomination. The only per-site inputs are the header and bit bank
obtained from the selected calendar. -/
theorem VirtualPairs.active_root {ex lanes : ℕ} (Y : State ex lanes) (v : Y.network.Site)
    (m : Memory (D.geometry n).w) (state : BurstRAM.Word (D.geometry n).w)
    (bits : Fin (∑ j, TerminalPrefix.width Y j) → Bool)
    (inputs : TerminalProgram.RootInputs Y v degree pub hdr state m bits)
    (large : 3 ≤ n) (fit : PairNativeGeometry.Fits D.numerator D.denominator n (D.geometry n).w) :
    VertexImage.RootRun A₀ M₀ m state degree ex
      (NativeOperands.work (NativeCache.args D.constants) D.numerator D.denominator (D.geometry n)+76)
      (VertexRootPacket.packet Y (TerminalRootGather.Layout.ofHeader degree pub hdr state m) v bits)
      (LeafVisit.cacheWords aux (CursorBounds.virtualBits D.addressFactor n) (roundedUp 1 4 n)) := by
  have hfitted := (V.counts i (PairedChain.headers adv ξ i) (physicalNomination rfl μ)).fits
  let M := M₀
  let A := A₀
  let start := M.program.start state
  have heads : TerminalSiteStart.headerWord M.publicData = hdr := headerWord_eq_header _
  have input : TerminalProgram.RootInputs Y v degree M.publicData (TerminalSiteStart.headerWord M.publicData) state m bits :=
    heads ▸ inputs
  have mem : start.privateMem = fun _ => 0 := rfl
  have here : start.pc = A.entry .bootstrap := by
    unfold start M A VertexImage.template
    rfl
  let A' : Placement (segments (VertexGeometry.segment D.constants degree D.numerator D.denominator)
      TerminalRootGather.segment LeafRole.segment (ShrinkVertexImage.shrinkSegment B order)
      (RefreshVertex.refreshSegment B (RefreshBlockPlan.order B) (RefreshBlockPlan.shape B).stride order))
      (Fintype.card (PC S₀)) (Fintype.card (Reg S₀)) := A
  have proof := VertexImage.active_root D.constants degree D.numerator D.denominator A' (V.layout i) aux M m start Y v bits
    D.denominator_pos D.address_pos large rfl fit (V.literal i) (V.scratch i) hfitted rfl V.cap.tags V.cap.capFits rfl
    (template_contains S₀ pub) here mem input.active input.rootPos input.rootBound input.cache input.numbering input.rows
    input.bank input.fits input.deg input.width input.header input.heads input.wires
  simp only [headerWord_eq_header] at proof
  obtain ⟨t,ht₀,out,es,ready,time,probes,det,stable,reads,run⟩ := proof
  have geom : AssemblerPublic.geometry D.addressFactor n (D.geometry n).H = D.geometry n := rfl
  have st : start.persistent = state := rfl
  have words : M.publicData = pub := rfl
  rw [geom] at ht₀
  simp only [st,words] at ready time probes reads
  exact ⟨t,ht₀,out,es,ready,time,probes,det,stable,reads,run⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
