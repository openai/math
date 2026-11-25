import OAI.Computability.BorderVNP.CubeISAOwnedStrictSide
import OAI.Computability.BorderVNP.CubeISAOwnedPacketRowInverse
import OAI.Computability.BorderVNP.CubeScatterCrossKeys

/-! # Inverting a full native strict side into its physical bits

Extend the actual finite chronological word to a tape. Its owned packet bits
give a physical realization with the same routed input streams. The resulting
native execution is unique all the way through both ordered singleton passes
and the final directory stores.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open Cube Cube.Scatter Physical Physical.Owned Cube.Tally VPVNP.BurstRAM DiagonalResidueRAM Owned

variable {w n d blocks b h K s : ℕ}

/-- The entire strict-side traversal uses only ordinary register, memory and binary-choice instructions. -/
theorem strictSide_nativeOnly (n b h K s : ℕ) : (strictSide n b h K s).nativeOnly = true := by
  have setup := (OwnedRowSetup.packet n b h K s).nativeOnly_of_unsigned (OwnedRowSetup.packet_unsigned ..)
  have vertices := (OwnedVertex.vertexRow n).nativeOnly_of_unsigned (vertexRow_frame n).1
  have swap : OwnedRowSetup.swap.nativeOnly = true := by decide
  simp only [strictSide,strictScatter,packetStage,doubleStage,Code.nativeOnly,setup,
    PacketRowData.loop_nativeOnly,singleStage_nativeOnly,swap,vertices,Bool.and_self]

/-- All fetched PCs in the complete strict-side program carry the native opcode tag. -/
theorem strictSide_native (n b h K s : ℕ) : ∀ pc, (strictSide n b h K s).program.tag pc = .native :=
  Code.program_tag_native _ (strictSide_nativeOnly n b h K s)

variable (D : PacketRowData n d blocks b h K s) (A : SideData n d blocks b h)

/-- The complete public crossing list is invariant under changing private physical words. -/
theorem crossing_exterior (x z) (outside : D.KeepsExterior x z) :
    commonCrossings b D.axis D.pair D.select z (fun q => A.value q.1.val q.2) =
      commonCrossings b D.axis D.pair D.select D.supply (fun q => A.value q.1.val q.2) := by
  have packet (p : Packet n d blocks) : crossingStream b (D.select p) D.axis (z p) =
      crossingStream b (D.select p) D.axis (D.supply p) := by
    simp only [crossingStream_eq_keys]
    apply List.map_congr_left
    intro q _
    exact (outside p).2.2 (q.1,D.axis) q.2 (.inl rfl)
  simp only [commonCrossings,packet]

/-- Every true normal return produces the precise choices and memory of a physical
assignment agreeing with the incoming public words and the untouched side. -/
theorem strictSide_recover (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ)
    (r : Bank w) (m : Memory w) (ready : SideReady D A pub src r m)
    {es t mt} (run : Runs pub mac (strictSide n b h K s) r m es t mt) :
    ∃ x z, D.KeepsExterior x z ∧
      (∀ p, (D.body p).map Position.routed = ((D.withWords x z).body p).map Position.routed) ∧
      TraceOK es (rowChoices packetTrialValid (D.withWords x z).choices) es.length ∧
      traceCost es ≤ sideCost D A ∧ SideResult (D.withWords x z) A src r m t mt := by
  let bs := es.flatMap TeamRAM.Event.choices
  obtain ⟨x,z,outside,routed,tape⟩ := D.realize_tape (ChoiceTape.extend bs)
  let E := D.withWords x z
  have streams := crossing_exterior D A x z outside
  have inputs : SideReady E A pub src r m := {ready with crosses := streams ▸ ready.crosses}
  obtain ⟨fs,y,my,canon,tr,cost,post⟩ := strictSide_run E A pub mac src r m inputs
  obtain ⟨a,a',compat⟩ := ChoiceTape.compatible bs (ChoiceTape.offset D.privateWidth (packetTrials n d blocks))
  have agree := (congrArg (· ++ a) (tr.2.1.trans tape)).trans compat
  obtain ⟨rfl,rfl,rfl⟩ := unique_returns (strictSide_native n b h K s) canon run agree
  exact ⟨x,z,outside,routed,tr,cost,post⟩

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI
