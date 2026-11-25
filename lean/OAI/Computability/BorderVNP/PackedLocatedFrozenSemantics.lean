import OAI.Computability.BorderVNP.PackedLocatedFrozenEmission
import OAI.Computability.BorderVNP.PackedFrozenProfileTable

/-! # Semantics and native output words of the table at its physical addresses -/

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

variable (wr : WidthRanges S (d+1) T (60*logWidth r n)) (hm : 0 < «m») (paid : plan.TapeWithin S wr hm)
    (qpos : 1≤Q) (hpos : 1≤logWidth r n) (wordEq : b.physical.word n=(logWidth r n)^(E+2))
    (window : NativeGeometryWindow (8*(11920000+1500000+16008100*A+37)) (4*(E+2)) n r (b.physical.word n) (R+1)
      (GridHosts.tileCount (Fintype.card (Cube D)) d) ((fan S)^T*GridHosts.tileCount (Fintype.card (Cube D)) d)
      (routingRows (boundaryShape S (d+1) T) (CoverScale.sites (Cube D) (EnrichedOuter.depth S (d+1) T))
        ((fan S)^T*GridHosts.tileCount (Fintype.card (Cube D)) d) ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d)))
    (φ : K →+* F) (q : ℕ) (adv : ℕ → ℕ) (c k factor : ℕ) (batch : r=stretch b.ρ n)
    (install : SignedReaderInstallAt (aux:=φ ∘ cube.table) (q:=q) cube b (cube.signedSiteProgram e) adv c k factor
      (4*(E+2)) (8*(11920000+1500000+16008100*A+37)) n)

local notation3 (prettyPrint := false) "located₁" => plan.locatedFrozenTable G order position W cube b initial l size A
  wr hm paid count qpos hpos wordEq hg shortLink sitePos inputs window φ q adv c k factor batch install
local notation3 (prettyPrint := false) "packet₁" late => locatedFrozenEmission G order position W cube b initial l size A
  count hg shortLink sitePos inputs late
local notation3 (prettyPrint := false) "width₁" => fun i => Fintype.card (Machine.Guess S (d+1) (fun _ _ => short) i)
local notation3 (prettyPrint := false) "slots₁" => fun i => Fintype.equivFin (Machine.Guess S (d+1) (fun _ _ => short) i)
local notation3 (prettyPrint := false) "input₁" => fun _ : Unit => false
local notation3 (prettyPrint := false) "base₁" => plan.frozenStart G order position Unit
local notation3 (prettyPrint := false) "header₁" => WorkWords.grouped (CoverScale.sites (Cube D) (d+1))
  (copies*GridHosts.inputBlockWidth r n axes d)
local notation3 (prettyPrint := false) "key₁" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "steps₁" => plan.compiled.tapeSteps fmt header₁ key₁ wr hm
local notation3 (prettyPrint := false) "hist₁" => compile steps₁ T le_rfl (repeatLeaf (fan S) base₁ T)
local notation3 (prettyPrint := false) "order₁" => broadcastOrder (fan S) width₁ slots₁ T
local notation3 (prettyPrint := false) "fit₁" => plan.profile_order_fits width₁ slots₁

/-- The public startup, directory pointers, physical task and gate lowering
are those of the original signed emitter before any live pin is supplied. -/
theorem locatedFrozenTable_source :
    (located₁).outputs=(packet₁ G).outputs ∧ (located₁).directories=(packet₁ G).directories ∧
      (packet₁ G).destination=Allocation.dest (initial.next+7*(dir).candidates) profileCap ceiling (located₁).outputs w ∧
      (packet₁ G).task=b.frozenSignedTask cube n l size head initial (dir) profileCap ceiling (located₁).outputs w
        (located₁).directories ∧
      (located₁).raw=geometryTable hist₁ order₁ fit₁ (packet₁ G).emitter input₁ := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

variable (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables F)
local notation3 (prettyPrint := false) "seed₁" => plan.frozenLeaf G order position W tag sites edges ports table input₁
local notation3 (prettyPrint := false) "geo₁" => (plan.execute G order position Unit).choose
local notation3 (prettyPrint := false) "code₁" => plan.compiled.machine.nativeCode seed₁ geo₁ input₁ rfl width₁ slots₁ fit₁

set_option maxHeartbeats 5000000 in
/-- Characterize all raw inputs of the actual installed table by the unique
original history, including every unused bit and each rejected profile. -/
theorem locatedFrozenTable_valid (raw : Fin (profileReserve r n) → Bool) :
    GeometryOutput.validBit ((located₁).raw.reserve ceiling) (Sum.elim raw Fin.elim0)=true ↔
      ∃! h : (packHistory seed₁ plan.compiled.machine.epoch T).Index,(code₁ h).val=raw := by
  exact plan.frozenProfile_valid G order position W tag sites edges ports table input₁ wr hm width₁ slots₁ fit₁
    (packet₁ G).emitter ceiling raw

set_option maxHeartbeats 6000000 in
/-- Read every actual output of the located table on an original history.
The same equality holds after installing the late literal into the template. -/
theorem locatedFrozenTable_words {latePins lateInner : ℕ} {Late : Type} (late : Wiring R r time latePins link lateInner n Late)
    (same : late.program=G.program) (h : (packHistory seed₁ plan.compiled.machine.epoch T).Index) :
    nativeTableWords ((located₁).raw.reserve ceiling) (code₁ h).val=fun i =>
      ParseBatchSort.value (fun j => (packet₁ late).emitter.eval (Sum.elim (Sum.elim input₁ (code₁ h).val)
        (output steps₁ T le_rfl (repeatLeaf (fan S) base₁ T) input₁ (plan.compiled.machine.packBits seed₁ T le_rfl h))) (i,j)) := by
  rw [locatedFrozenEmission_program G order position W cube b initial l size A count hg shortLink sitePos inputs late same]
  exact plan.frozenProfile_words G order position W tag sites edges ports table input₁ wr hm width₁ slots₁ fit₁
    (packet₁ G).emitter ceiling h

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
