import OAI.Computability.BorderVNP.PackedLocatedFrozenTable

/-! # The output shape of the located signed gate table -/

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
local notation "hooks" => Fintype.card (e.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
local notation3 (prettyPrint := false) "num" => fun z : e.Entry => cube.scalarNumber e (.inl z)
local notation3 (prettyPrint := false) "fmt" => Boundary.seedFormat G order position copies
/-- The installed gate table publishes the full routing prefix, all 37 controls,
the term-dependent packet capacity and both padded original-bundle arrays. -/
theorem locatedFrozenTable_output_shape
    (wr : WidthRanges S (d+1) T (60*logWidth r n)) (hm : 0 < m) (paid : plan.TapeWithin S wr hm)
    (count : (fan S)^T*copies=R+1) (qpos : 1 ≤ Q) (hpos : 1 ≤ logWidth r n)
    (wordEq : b.physical.word n = (logWidth r n)^(E+2))
    (hg : 0 < GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d)
    (shortLink : GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d ≤ link)
    (sitePos : 0 < (sh).sites)
    (inputs : SignedPacketInputBounds S (d+1) T cells live short w (logWidth r n) E A hooks fmt
      {dir with sites := tiles,entries := J} rfl num)
    (window : NativeGeometryWindow (8*(11920000+1500000+16008100*A+37)) (4*(E+2)) n r w (R+1) tiles J
      (routingRows sh cells J live))
    (φ : K →+* F) (q : ℕ) (adv : ℕ → ℕ) (c k factor : ℕ) (batch : r = stretch b.ρ n)
    (install : SignedReaderInstallAt (aux:=φ ∘ cube.table) (q:=q) cube b (cube.signedSiteProgram e)
      adv c k factor (4*(E+2)) (8*(11920000+1500000+16008100*A+37)) n) :
    let t := plan.locatedFrozenTable G order position W cube b initial l size A wr hm paid count qpos hpos
      wordEq hg shortLink sitePos inputs window φ q adv c k factor batch install
    let depth := BottomReports.BundleSort.markedDepth cells J
    ∃ pack, t.outputs = signedGridOutputCount cables cells J live 37 pack+(2^depth+2^depth) := by
  exact ⟨_,rfl⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
