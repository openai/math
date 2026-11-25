import OAI.Computability.BorderVNP.PackedFrozenPacketEmitterCharge
import OAI.Computability.BorderVNP.PackedFrozenPacketDirectories
import OAI.Computability.BorderVNP.PackedFrozenBundleShape
import OAI.Computability.BorderVNP.DiagonalFrozenSignedScalarNumbers
import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask

/-! # The signed gate table at its own absolute task and directory addresses -/

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

/-- A public table and its real startup receipt. The task can be recovered
from the directory and output arity before filling any original assignment. -/
structure LocatedFrozenTable (reserve word ceiling n r teams tiles origins : ℕ)
    (installation : ℕ → ℕ → Prop) where
  /-- Total native words in the 37-control packet and its two appended sort banks. -/
  outputs : ℕ
  /-- Absolute addresses of the descriptor rows and the two original-bundle banks. -/
  directories : SignedTaskArena.GeometryDirectories
  /-- Lowered gate table before padding to the selected gate ceiling. -/
  raw : Table (Fin reserve ⊕ Fin 0) outputs word
  /-- The reader can install precisely this gate count and emitted word count. -/
  startup : installation raw.size outputs
  /-- The measured lowering fits its reserved gate block. -/
  raw_bound : raw.size ≤ ceiling
  /-- Padding the original lowering consumes exactly the reserved block. -/
  reserved_size : (raw.reserve ceiling).size = ceiling
  /-- Geometry evaluation, packet movement and the directory scan fit their common clock. -/
  timed : (GeometryAdviceRate.ticks ceiling reserve outputs word word+
    packetWords ceiling reserve outputs word*word+reserve+deliveryScanTicks origins teams tiles : ℕ) <
    (r:ℝ)*(n:ℝ)^(93/100:ℝ)
  /-- Both geometry evaluation and the serialized packet fit the batch budget. -/
  packet_bound : GeometryAdviceRate.ticks ceiling reserve outputs word word+
    packetWords ceiling reserve outputs word*word ≤ r*TeamScales.width n (95/100:ℝ)

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

/-- Lower the actual augmented public history and its full terminal emitter.
The output arity fixes the destination before the public gate instructions
are generated. Thus the task's control words and sorted-bank pointers can
be used as gate constants without referring to a later public history. -/
noncomputable def locatedFrozenTable
    (wr : WidthRanges S (d+1) T (60*logWidth r n)) (hm : 0 < m) (paid : plan.TapeWithin S wr hm)
    (count : (fan S)^T*copies=R+1) (qpos : 1 ≤ Q) (hpos : 1 ≤ logWidth r n)
    (wordEq : b.physical.word n = (logWidth r n)^(E+2))
    (hg : 0 < GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d)
    (shortLink : GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d ≤ link)
    (sitePos : 0 < (sh).sites)
    (inputs : SignedPacketInputBounds S (d+1) T cells live short w (logWidth r n) E A hooks fmt
      {dir with sites := tiles,entries := J} rfl num)
    (window : NativeGeometryWindow (8*(11920000+1500000+16008100*A+37)) (4*(E+2)) n r w (R+1) tiles J
      (routingRows sh cells J live)) :
    let runSite := cube.signedSiteProgram e
    ∀ (φ : K →+* F) (q : ℕ) (adv : ℕ → ℕ) (c k factor : ℕ),
      r = stretch b.ρ n →
      SignedReaderInstallAt (aux:=φ ∘ cube.table) (q:=q) cube b runSite adv c k factor
        (4*(E+2)) (8*(11920000+1500000+16008100*A+37)) n →
      LocatedFrozenTable profileCap w ceiling n r (R+1) tiles J (fun gates o =>
        SignedTableStartupAt (aux:=φ ∘ cube.table) (q:=q) cube b runSite adv c k factor n
          gates ceiling ceiling o w desc) := by
  intro runSite φ q adv c k factor batch install
  classical
  let shape := inputs sitePos
  dsimp only at shape
  rw [←Nat.mul_assoc 6 (R+1) tiles,←Nat.mul_assoc 4 (R+1) tiles] at shape
  let hs := shape.2.2.2.2.choose
  let hf := shape.2.2.2.2.choose_spec.choose
  let dims := shape.2.2.2.2.choose_spec.choose_spec
  let room := shape.2.1
  let boxes := scheduledBoxes (dir) rfl (num) sitePos
  let tpl := template (prep) (lastTape) boxes hs hf
    (FinalReports.Spare.priv (C:=cells) (g:=hooks) (digits:=w) (E:=Fin J))
    (FinalReports.Spare.reports (C:=cells) (g:=hooks) (digits:=w) (E:=Fin J))
  let marked := BottomReports.BundleSort.markedDepth cells J
  let o := signedGridOutputCount cables cells J live 37 (Total tpl.publicDepth tpl.chunkDepth)+(2^marked+2^marked)
  let origin := Allocation.dest (initial.next+7*(dir).candidates) profileCap ceiling o w
  let dirs := frozenPacketDirectories tpl origin cables J live marked
  let task := b.frozenSignedTask cube n l size head initial (dir) profileCap ceiling o w dirs
  let ctrl : Fin 37 → Fin (2^w) := fun i => Fin.ofNat _ (task.controls i.val)
  let banks := task.cube.cellWriter initial.frame (RoutingOutputs.controlsBase origin cables cells J live) 0
  let owners := Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d+1) T+1))
  let widths := fun i => Fintype.card (Machine.Guess S (d+1) (fun _ _ => short) i)
  let slots := fun i => Fintype.equivFin (Machine.Guess S (d+1) (fun _ _ => short) i)
  let x := fun _ : Unit => false
  let emit := frozenPacketWithBundles (reserve:=profileCap) S G order position Unit G count owners
    room.2.2.2.2.2 (Nat.le_of_lt (Nat.lt_trans (Nat.lt_succ_self cells) room.2.2.2.2.1)) hg shortLink room.2.2.2.1
    (dir) (num) sitePos room.2.2.2.1 task.cube.cellBank task.cube.cellStride task.p.privateGap desc hooks w
    ctrl hs hf room.2.2.2.1 dims.1 room.2.2.2.2.1 shape.2.2.1 dims.2.2.1 origin (head*logWidth r n)
    banks marked (W.frozenBundleShapes position ((fan S)^T) copies)
  let receipt := frozenPacketWithBundles_clock S G order position Unit G count owners
    room.2.2.2.2.2 (Nat.le_of_lt (Nat.lt_trans (Nat.lt_succ_self cells) room.2.2.2.2.1)) hg shortLink room.2.2.2.1
    (dir) (num) sitePos room.2.2.2.1 task.cube.cellBank task.cube.cellStride task.p.privateGap desc hooks w
    ctrl hs hf room.2.2.2.1 dims.1 room.2.2.2.2.1 shape.2.2.1 dims.2.2.1 origin (head*logWidth r n)
    banks (W.frozenBundleShapes position ((fan S)^T) copies) plan wr hm widths slots E A 37 hpos wordEq qpos paid
    room.2.1 room.2.2.1 le_rfl dims.2.2.2.1 dims.2.2.2.2.1 dims.2.2.2.2.2.1 dims.2.2.2.2.2.2.1
    dims.2.2.2.2.2.2.2 shape.1 le_rfl window x
  let header := grouped (CoverScale.sites (Cube D) (d+1)) (copies*GridHosts.inputBlockWidth r n axes d)
  let key := Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
  let hist := compile (plan.compiled.tapeSteps fmt header key wr hm) T le_rfl
    (repeatLeaf (fan S) (plan.frozenStart G order position Unit) T)
  let raw := geometryTable hist (broadcastOrder (fan S) widths slots T) (plan.profile_order_fits widths slots) emit x
  have positive : 1 ≤ w := wordEq.symm ▸ Nat.pow_pos hpos
  let readOrder := broadcastOrder (fan S) widths slots T
  let slotsFit := plan.profile_order_fits widths slots
  let sourceWidth := desc
  have startup : SignedTableStartupAt (aux:=φ ∘ cube.table) (q:=q) cube b runSite adv c k factor n
      raw.size ceiling ceiling o w desc := by
    have boot : SignedTableStartupAt (aux:=φ ∘ cube.table) (q:=q) cube b runSite adv c k factor n
        raw.size (raw.reserve ceiling).size ceiling o w desc := by
      subst r
      exact install hist readOrder slotsFit emit x positive receipt sourceWidth
    have eqn : (raw.reserve ceiling).size=ceiling := receipt.2.1
    rwa [eqn] at boot
  exact ⟨o,dirs,raw,startup,receipt.1,receipt.2.1,receipt.2.2.1,receipt.2.2.2⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
