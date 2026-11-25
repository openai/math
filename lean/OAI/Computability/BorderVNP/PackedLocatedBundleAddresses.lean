import OAI.Computability.BorderVNP.PackedLocatedEmitterOperands

/-! # Address the two original-bundle arrays in a located signed table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords
open Diagonal Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales VPVNP.VerifierNetwork TerminalCells GridHosts
open CellPacketGeometry CellPacketGeometry.History CellPacketGeometry.LiveWords CellSparse.Packet
open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator GeometryAdvice GeometryFrameEncoding GeometryAdviceRate
open RoutingISA.Transmission TeamContraction.ProcessorSlots
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

set_option maxHeartbeats 2500000
set_option maxRecDepth 8000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {n r d T copies head Q : ℕ} (plan : SeedPlan S n r d T copies head Q)
    {R time pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring R r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {g : ℕ} {len : Fin n} {state : Fin g} (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
    (cube : FixedCube K) {extra E degree qa aa bb jj : ℕ} {scale : EpochScales S (cube.pred+1) extra}
    (b : JointSchedule.{0} scale (E+1) degree qa aa bb jj) (initial : StartupArena) (l size A : ℕ)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "J" => (fan S)^T*tiles
local notation "live" => (R+1)*tiles
local notation "short" => 60*logWidth r n
local notation "w" => b.physical.word n
local notation "cells" => CoverScale.sites (Cube D) (EnrichedOuter.depth S (d+1) T)
local notation3 (prettyPrint := false) "sh" => boundaryShape S (d+1) T
local notation3 (prettyPrint := false) "cables" => (sh).edges+4*(R+1)*tiles
local notation "desc" => seedDescriptionWidth n r axes d (head*logWidth r n)
  (BottomGridBank.bodyBudget (seedBoxCapacity n r axes d (Fintype.card (Direction axes))))
local notation3 (prettyPrint := false) "dir" => freeDirectory R r (G.program.length+time) link tiles
  (GridHosts.inputBlockWidth r n axes d) J desc
local notation "profileCap" => profileReserve r n
local notation "ceiling" => geometryGateCeiling (8*(11920000+1500000+16008100*A+37)) (4*(E+2)) r n
local notation "hooks" => Fintype.card (e.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
local notation3 (prettyPrint := false) "num" => fun z : e.Entry => cube.scalarNumber e (.inl z)
local notation3 (prettyPrint := false) "fmt" => Boundary.seedFormat G order position copies
local notation3 (prettyPrint := false) "epochFmt" => ProgramSchemas.epoch S (d+1) short fmt T
local notation3 (prettyPrint := false) "prep" => (epochFmt).schema.append (Sewn.schema (2*(sh).edges+6*(R+1)*tiles) short)
local notation3 (prettyPrint := false) "lastTape" => FinalTies.tieSchema cables live w

variable (count : (fan S)^T*copies=R+1)
    (hg : 0 < GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d)
    (shortLink : GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d ≤ link)
    (sitePos : 0 < (boundaryShape S (d+1) T).sites)
    (inputs : SignedPacketInputBounds S (d+1) T (CoverScale.sites (Cube D) (EnrichedOuter.depth S (d+1) T))
      ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n) (b.physical.word n) (logWidth r n) E A
      (Fintype.card (e.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width))
      (Boundary.seedFormat G order position copies)
      {freeDirectory R r (G.program.length+time) link (GridHosts.tileCount (Fintype.card (Cube D)) d)
        (GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d) ((fan S)^T*GridHosts.tileCount (Fintype.card (Cube D)) d)
        (seedDescriptionWidth n r (Fintype.card (Cube D)) d (head*logWidth r n)
        (BottomGridBank.bodyBudget (seedBoxCapacity n r (Fintype.card (Cube D)) d
          (Fintype.card (Direction (Fintype.card (Cube D))))))) with
        sites := GridHosts.tileCount (Fintype.card (Cube D)) d, entries := (fan S)^T*GridHosts.tileCount (Fintype.card (Cube D)) d}
      rfl (fun z : e.Entry => cube.scalarNumber e (.inl z)))


local notation3 (prettyPrint := false) "emission" late => locatedFrozenEmission G order position W cube b initial l size A
  count hg shortLink sitePos inputs late

set_option maxHeartbeats 8500000 in
/-- The dense signed packet starts at the true output destination. Both
original-bundle banks immediately follow it in the task's own directory,
with one full marked row for each padded sorter slot. -/
theorem locatedFrozenEmission_bundle_columns {latePins lateInner : ℕ} {Late : Type}
    (late : Wiring R r time latePins link lateInner n Late) :
    let z := emission late
    let ordinary := signedGridOutputCount cables cells J live 37 z.packetWords
    let depth := BottomReports.BundleSort.markedDepth cells J
    z.outputs=ordinary+(2^depth+2^depth) ∧ z.directories.bundlePayload=z.destination+ordinary ∧
      z.directories.bundleInverse=z.destination+ordinary+2^depth := by
  intro z ordinary depth
  obtain ⟨vf,cf,extend,hs,hf,sitesFit,sw,pad,core,indexBits,full,dirs,_⟩ :=
    locatedFrozenEmission_operands G order position W cube b initial l size A count hg shortLink sitePos inputs late
  let boxes := scheduledBoxes (dir) rfl (num) sitePos
  let tpl := template (prep) (lastTape) boxes hs hf
    (FinalReports.Spare.priv (C:=cells) (g:=hooks) (digits:=w) (E:=Fin J))
    (FinalReports.Spare.reports (C:=cells) (g:=hooks) (digits:=w) (E:=Fin J))
  have room := (frozenPacketDirectories_locations tpl z.destination cables J live depth).2.2.2
  change z.packetWords=Total tpl.publicDepth tpl.chunkDepth at core
  change z.directories=frozenPacketDirectories tpl z.destination cables J live depth at dirs
  dsimp only [ordinary]
  rw [core,dirs]
  exact ⟨full,room.1,room.2⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
