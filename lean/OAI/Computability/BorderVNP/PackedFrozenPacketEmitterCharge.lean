import OAI.Computability.BorderVNP.DiagonalChargedFrozenOutput
import OAI.Computability.BorderVNP.DiagonalNativeGeometryWindow
import OAI.Computability.BorderVNP.PackedFrozenSeedExecute
import OAI.Computability.BorderVNP.PackedFrozenNativeSeedInterface
import OAI.Computability.BorderVNP.PackedTerminalDirectStagedCost
import OAI.Computability.BorderVNP.PackedSignedBundleGateCost
import OAI.Computability.BorderVNP.PackedTerminalSignedHeaderDepth
import OAI.Computability.BorderVNP.PackedFrozenSignedEmitter
import OAI.Computability.BorderVNP.PackedTerminalSignedGridEmitterCost

/-! # Cost of the fixed signed emitter before every private verifier input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Shortening.PreparedBins
open Packing.PhysicalEpochs
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales VPVNP.VerifierNetwork
open TerminalCells FieldExport GridHosts Diagonal.ExternalSew.RowTrace Packing.CellAddressCircuit Packing.SewnField
open scoped Classical BorderVNP.Epoch.Cube
open CellPacketGeometry CellPacketGeometry.History CellPacketGeometry.History.Native CellPacketGeometry.LiveWords
open Packing.CellAddresses Packing.CellAddressPhysical Packing.RoutingOutputs CellSparse.Packet
open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator ParseBatchSort
attribute [local instance] portFintype
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {n r d T copies : ℕ}
    {teams time pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (σ : Type) [Fintype σ] {reserve : ℕ}
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d

local notation "w" => 60*logWidth r n
local notation "sh" => boundaryShape S (d+1) T
local notation "fmt" => Boundary.seedFormat G order position copies
local notation3 (prettyPrint := false) "epochFmt" => ProgramSchemas.epoch S (d+1) w fmt T
local notation "offs" => flatOffset (compiledOffset S (d+1)) T
local notation "J" => (fan S)^T * tiles
local notation "g₁" => inputBlockWidth r n axes d
variable {R rTime rPins ell rInner : ℕ} {Wire : Type}
    (actual : Wiring R r rTime rPins ell rInner n Wire) (count : (fan S)^T*copies=R+1)
    {cells k packetWidth : ℕ} (cellNumber : (Cube D → Deck (EnrichedOuter.depth S (d+1) T+1)) ≃ Fin cells)
    (vf : (boundaryShape S (d+1) T).sites ≤ 2^(60*logWidth r n)) (cf : cells ≤ 2^k)
    (hg : 0 < inputBlockWidth r n (Fintype.card (Cube D)) d) (short : inputBlockWidth r n (Fintype.card (Cube D)) d ≤ ell)
    (extend : 60*logWidth r n ≤ packetWidth)
    (dir : Directory.Layout) (number : e.Entry → ℕ) (sitePos : 0 < (boundaryShape S (d+1) T).sites)
    (ownerFits : k ≤ packetWidth)
local notation3 (prettyPrint := false) "publicDir" => {dir with sites := tiles, entries := J}
local notation3 (prettyPrint := false) "boxes₁" => scheduledBoxes publicDir rfl number sitePos
local notation3 (prettyPrint := false) "old₁" => (originalPins sitePos offs : Fin J → Fin (sh).sites)
local notation3 (prettyPrint := false) "schema₁" => (epochFmt).schema.append (Sewn.schema (2*(sh).edges+6*(R+1)*tiles) w)
local notation3 (prettyPrint := false) "final₁" => FinalTies.tieSchema ((sh).edges+4*(R+1)*tiles) ((R+1)*tiles) packetWidth

variable {qbits tagCap control : ℕ} (arena stride gap desc gadgets digits : ℕ) (controls : Fin control → Fin (2^packetWidth))
    (hs : ∀ j, (((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))).tags j).length≤tagCap) (hf : ∀ j, ((FinalTies.tieSchema ((boundaryShape S (d+1) T).edges+4*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d)
      ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) packetWidth).tags j).length≤tagCap)
    (keyFits : 60*logWidth r n≤qbits) (sitesFit : (boundaryShape S (d+1) T).sites<2^qbits)
    (keysFit : cells+1<2^k) (sw : ∀ j, ((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))).width j≤packetWidth)
    (pad : (roster (boundaryShape S (d+1) T).sites ((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))) (FinalTies.tieSchema ((boundaryShape S (d+1) T).edges+4*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d)
      ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) packetWidth)).length<2^qbits) (dest hdr : ℕ)

local notation3 (prettyPrint := false) "priv₁" => FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J)
local notation3 (prettyPrint := false) "reports₁" => FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J)
local notation3 (prettyPrint := false) "tpl₁" => template schema₁ final₁ boxes₁ hs hf priv₁ reports₁

open private oldWire from OAI.Computability.BorderVNP.PackedTerminalStagedFields

local notation3 (prettyPrint := false) "rep₀" => FinalReports.Spare.reports (C:=cells) (g:=gadgets)
  (digits:=digits) (E:=Fin J)
local notation3 (prettyPrint := false) "priv₀" => FinalReports.Spare.priv (C:=cells) (g:=gadgets)
  (digits:=digits) (E:=Fin J)
local notation3 (prettyPrint := false) "tpl₀" => template schema₁ final₁ boxes₁ hs hf priv₀ rep₀
local notation3 (prettyPrint := false) "packet₀" => frozenPacketEmitter (reserve:=reserve) S G order position σ
  actual count cellNumber vf cf hg short extend dir number sitePos ownerFits arena stride gap desc gadgets digits
  controls hs hf keyFits sitesFit keysFit sw pad dest hdr
local notation "liveCount" => (R+1)*tiles
local notation3 (prettyPrint := false) "written" => signedGridOutputCount ((sh).edges+4*(R+1)*tiles)
  cells J liveCount control (Total (tpl₀).publicDepth (tpl₀).chunkDepth)

omit [Fintype Edge] in
/-- The fixed signed emitter and all bits of its native output satisfy the
reservation charge, with the real original descriptor slots, spare cell,
absolute directory marks and widened source. The native clock is independent
of the later chart or any potentially malformed profile word. -/
theorem frozenPacketEmitter_charge (E A controlsCap : ℕ) (hpos : 1 ≤ logWidth r n)
    (nv : packetWidth = (logWidth r n)^(E+2))
    (keyRoom : Cover.AddressCircuit.keyWidth axes (EnrichedOuter.depth S (d+1) T+1) ≤ packetWidth)
    (logs : Nat.clog 2 (routingRows sh cells J liveCount) ≤ packetWidth)
    (qFit : qbits ≤ packetWidth) (wp : (tpl₀).publicDepth ≤ packetWidth)
    (wd : (tpl₀).chunkDepth ≤ packetWidth) (wb : (tpl₀).recordDepth ≤ packetWidth)
    (wh : Nat.clog 2 ((roster (sh).sites schema₁ final₁).length+(cells+1)) ≤ packetWidth)
    (wl : Nat.clog 2 (((sh).sites+1)+(roster (sh).sites schema₁ final₁).length) ≤ packetWidth)
    (volume : sourceVolume schema₁ final₁ boxes₁ rep₀ ≤
      A*routingRows sh cells J liveCount*(logWidth r n)^(max 2 (E+2)))
    (controlsFit : control ≤ controlsCap) :
    (packet₀).size+written*packetWidth ≤
      (8*(11920000+16008100*A+controlsCap))*routingRows sh cells J liveCount*(logWidth r n)^(4*(E+2)) := by
  exact signedGridEmitter_charge (X := σ) (reserve := reserve) (Move := allowedMoves (Cube D) S.budget)
    actual (show 0 < tiles from Fintype.card_pos) count hg short sh (factorEnum D) cellNumber cf epochFmt id
    vf (@groupRow ((fan S)^T) tiles offs) (fun _ => copies*g₁) (attachedName offs copies) FinalTies.routePresent
    extend ownerFits old₁ controls boxes₁ arena stride gap desc gadgets digits
    (fun i => oldWire (FinalTies.sewnPresent (fieldSewParams actual axes d) FinalTies.routePresent i))
    (fun _ => true) (.inr true) hs hf keyFits sitesFit (Nat.lt_trans (Nat.lt_succ_self cells) keysFit)
    sw (fun _ => le_rfl) (fun _ => Fin.last cells) (fun j => .inl (.inr j)) pad
    (Retained.packetBase dest ((sh).edges+4*(R+1)*tiles) cells J liveCount control) hdr
    (logWidth r n) E A controlsCap hpos nv keyRoom logs qFit wp wd wb wh wl volume controlsFit

local notation3 (prettyPrint := false) "pre" => TerminalCells.fields (Move := allowedMoves (Cube D) S.budget) (q := axes)
  (d := EnrichedOuter.depth S (d+1) T) (E := (sh).edges) vf cf (@groupRow ((fan S)^T) tiles offs) (fun _ => copies*g₁)
local notation3 (prettyPrint := false) "raw" => FieldExport.fields pre (fieldSewParams actual axes d) (attachedName offs copies)
local notation3 (prettyPrint := false) "route₀" => Retained.Terminal.route (X := σ) (reserve := reserve) epochFmt
local notation3 (prettyPrint := false) "extent₀" => Retained.Terminal.width (X := σ) (reserve := reserve) epochFmt true
local notation3 (prettyPrint := false) "primary" => withSewnFields (boundFrame (factorEnum D) cellNumber cf route₀ extent₀)
local notation3 (prettyPrint := false) "signedSource" => stagedSource raw primary
local notation3 (prettyPrint := false) "signedFields" => Fields.widenWidths (stagedFields raw) extend (Sum.inr false)

variable (bankLayout : CellBanks.Layout)
    (shapes : Fin ((fan S)^T*GridHosts.tileCount (Fintype.card (Cube D)) d) → BottomReports.BundleSort.Shape)
local notation3 (prettyPrint := false) "banks" => ({ bankLayout with cells := cells } : CellBanks.Layout)
local notation3 (prettyPrint := false) "valid" => VPVNP.VerifierNetwork.Frame.initial (fun _ : Unit => Sum.inr true)
local notation3 (prettyPrint := false) "headers" => BottomReports.BundleSort.headerBanks banks signedFields (BottomReports.BundleSort.markedDepth cells J) old₁
  desc gap shapes valid


local notation3 (prettyPrint := false) "fullPacket" => frozenPacketWithBundles (reserve:=reserve) S G order position σ
  actual count cellNumber vf cf hg short extend dir number sitePos ownerFits arena stride gap desc gadgets digits
  controls hs hf keyFits sitesFit keysFit sw pad dest hdr bankLayout (BottomReports.BundleSort.markedDepth cells J) shapes

omit [Fintype Edge] in
/-- All gates and physical output bits of the actual signed terminal also
pay for its two marked-sort banks. The gate bound includes a further execution
of the staged source when the banks are appended to the first output frame. -/
theorem frozenPacketWithBundles_charge (E A controlsCap : ℕ) (hpos : 1 ≤ logWidth r n)
    (nv : packetWidth = (logWidth r n)^(E+2))
    (keyRoom : Cover.AddressCircuit.keyWidth axes (EnrichedOuter.depth S (d+1) T+1) ≤ packetWidth)
    (logs : Nat.clog 2 (routingRows sh cells J liveCount) ≤ packetWidth)
    (qFit : qbits ≤ packetWidth) (wp : (tpl₀).publicDepth ≤ packetWidth)
    (wd : (tpl₀).chunkDepth ≤ packetWidth) (wb : (tpl₀).recordDepth ≤ packetWidth)
    (wh : Nat.clog 2 ((roster (sh).sites schema₁ final₁).length+(cells+1)) ≤ packetWidth)
    (wl : Nat.clog 2 (((sh).sites+1)+(roster (sh).sites schema₁ final₁).length) ≤ packetWidth)
    (volume : sourceVolume schema₁ final₁ boxes₁ rep₀ ≤
      A*routingRows sh cells J liveCount*(logWidth r n)^(max 2 (E+2)))
    (controlsFit : control ≤ controlsCap) :
    let b := BottomReports.BundleSort.markedDepth cells J
    let o := written+(2^b+2^b)
    (fullPacket).size+o*packetWidth ≤
      (8*(11920000+1500000+16008100*A+controlsCap))*routingRows sh cells J liveCount*(logWidth r n)^(4*(E+2)) := by
  intro b o
  let rows := routingRows sh cells J liveCount
  have prefixCost := frozenPacketEmitter_charge (reserve:=reserve) S G order position σ actual count cellNumber vf cf
    hg short extend dir number sitePos ownerFits arena stride gap desc gadgets digits controls hs hf keyFits sitesFit keysFit sw
    pad dest hdr E A controlsCap hpos nv keyRoom logs qFit wp wd wb wh wl volume controlsFit
  have rowCap : 1+CellAddressCircuit.count (sh).sites ((sh).edges+(fieldSewParams actual axes d).slots) liveCount cells+J+liveCount ≤ rows := by
    dsimp only [rows,routingRows,fieldSewParams,Params.slots]
    rw [Nat.mul_assoc 4]
  have smallRows : 1+CellAddressCircuit.count (sh).sites ((sh).edges+(fieldSewParams actual axes d).slots) liveCount cells ≤ rows :=
    (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans rowCap)
  have sourceCost := direct_staged_cost (X:=σ) (reserve:=reserve) (Move:=allowedMoves (Cube D) S.budget)
    (factorEnum D) cellNumber cf epochFmt (fieldSewParams actual axes d) vf (@groupRow ((fan S)^T) tiles offs)
    (fun _ => copies*g₁) (attachedName offs copies) smallRows keyRoom ownerFits extend logs
  exact Retained.appendBundle_charge packet₀ signedSource banks signedFields old₁ desc gap shapes (Sum.inr true)
    hpos nv rowCap ⟨extend,ownerFits,logs⟩ prefixCost sourceCost

open Diagonal GeometryAdviceRate

variable {headerFactor multQ : ℕ} (plan : SeedPlan S n r d T copies headerFactor multQ)
    (wr : WidthRanges S (d+1) T (60*logWidth r n)) (hm : 0 < m)
    (widths : ℕ → ℕ)
    (ord : ∀ i, Machine.Guess S (d+1) (fun _ _ => 60*logWidth r n) i ≃ Fin (widths i))

local notation "head" => grouped (CoverScale.sites (Cube D) (d+1)) (copies*g₁)
local notation3 (prettyPrint := false) "key₀" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "source₀" => plan.frozenStart G order position σ
local notation3 (prettyPrint := false) "top" => compile (plan.compiled.tapeSteps fmt head key₀ wr hm) T le_rfl
  (repeatLeaf (fan S) source₀ T)
local notation3 (prettyPrint := false) "ord₀" => broadcastOrder (fan S) widths ord T
local notation3 (prettyPrint := false) "target" => frozenPacketWithBundles (reserve:=profileReserve r n) S G order position σ
  actual count cellNumber vf cf hg short extend dir number sitePos ownerFits arena stride gap desc gadgets digits
  controls hs hf keyFits sitesFit keysFit sw pad dest hdr bankLayout (BottomReports.BundleSort.markedDepth cells J) shapes

/-- Lower and run the full named signed geometry program, with its selected
augmented chronological history, on the very same bounded physical table
used to compute its own absolute addresses. Both original-bundle banks,
the cell packet, the public profile and the delivery scan enter the clock. -/
theorem frozenPacketWithBundles_clock (E A controlsCap : ℕ) (hpos : 1 ≤ logWidth r n)
    (nv : packetWidth = (logWidth r n)^(E+2)) (qpos : 1 ≤ multQ) (paid : plan.TapeWithin S wr hm)
    (keyRoom : Cover.AddressCircuit.keyWidth axes (EnrichedOuter.depth S (d+1) T+1) ≤ packetWidth)
    (logs : Nat.clog 2 (routingRows sh cells J liveCount) ≤ packetWidth)
    (qFit : qbits ≤ packetWidth) (wp : (tpl₀).publicDepth ≤ packetWidth)
    (wd : (tpl₀).chunkDepth ≤ packetWidth) (wb : (tpl₀).recordDepth ≤ packetWidth)
    (wh : Nat.clog 2 ((roster (sh).sites schema₁ final₁).length+(cells+1)) ≤ packetWidth)
    (wl : Nat.clog 2 (((sh).sites+1)+(roster (sh).sites schema₁ final₁).length) ≤ packetWidth)
    (volume : sourceVolume schema₁ final₁ boxes₁ rep₀ ≤
      A*routingRows sh cells J liveCount*(logWidth r n)^(max 2 (E+2)))
    (controlsFit : control ≤ controlsCap)
    (window : NativeGeometryWindow (8*(11920000+1500000+16008100*A+controlsCap)) (4*(E+2))
      n r packetWidth (R+1) tiles J (routingRows sh cells J liveCount)) (x : σ → Bool) :
    NativeGeometryReceipt (8*(11920000+1500000+16008100*A+controlsCap)) (4*(E+2)) n r packetWidth
      (R+1) tiles J top ord₀ (plan.profile_order_fits widths ord) target x := by
  let base := (plan.execute G order position σ).choose
  have measured := paid G order position base (plan.execute G order position σ).choose_spec.1
  have cardinal : Fintype.card (SeedSlot S n r d T) = broadcastWidth (fan S) widths T :=
    (Fintype.card_congr ord₀).trans (Fintype.card_fin _)
  change ((multQ*(top).size + Fintype.card (SeedSlot S n r d T) : ℕ) : ℝ) <
    r*(n:ℝ)^(92/100:ℝ) at measured
  rw [cardinal] at measured
  have packet := frozenPacketWithBundles_charge (reserve:=profileReserve r n) S G order position σ actual count cellNumber
    vf cf hg short extend dir number sitePos ownerFits arena stride gap desc gadgets digits controls hs hf keyFits
    sitesFit keysFit sw pad dest hdr bankLayout shapes E A controlsCap hpos nv keyRoom logs qFit wp wd wb wh wl volume controlsFit
  have size₀ : (top).size ≤ multQ*(top).size := Nat.le_mul_of_pos_left _ qpos
  have word : 1 ≤ packetWidth := nv.symm ▸ Nat.pow_pos hpos
  exact window top ord₀ (plan.profile_order_fits widths ord) target x word measured.le
    ((Nat.add_assoc ..).le.trans (Nat.add_le_add size₀ packet))

/-- Install the literal, descriptor directory, allocated byte lanes and true
branch time of the concrete scheduled packet. All serialized output words,
including the two marked-sort banks, refer to the same lowered table. -/
theorem frozenPacketWithBundles_startup (E A : ℕ) (hpos : 1 ≤ logWidth r n)
    (nv : packetWidth = (logWidth r n)^(E+2)) (qpos : 1 ≤ multQ) (paid : plan.TapeWithin S wr hm)
    (tagFormat : tagCap=ProgramSchemas.signedTagCapacity (e:=e)) (digitFormat : digits=packetWidth)
    (qFit : qbits ≤ packetWidth)
    (inputs : SignedPacketInputBounds S (d+1) T cells liveCount w packetWidth (logWidth r n) E A gadgets
      fmt publicDir rfl number)
    (controlsFit : control ≤ 37)
    (window : NativeGeometryWindow (8*(11920000+1500000+16008100*A+37)) (4*(E+2))
      n r packetWidth (R+1) tiles J (routingRows sh cells J liveCount)) (x : σ → Bool)
    {K₀ : Type} [Field K₀] (cube : FixedCube K₀) (φ : K₀ →+* K) (char : ℕ)
    {extra degree Q a₀ b₀ j : ℕ} {scale : EpochScales S (cube.pred+1) extra}
    (b : JointSchedule.{0} scale (E+1) degree Q a₀ b₀ j) (adv : ℕ → ℕ) (c adDeg factor : ℕ)
    (rEq : r=stretch b.ρ n) (wordEq : packetWidth=b.physical.word n)
    (install : SignedReaderInstallAt (aux:=φ ∘ cube.table) (q:=char) cube b (cube.signedSiteProgram e)
      adv c adDeg factor (4*(E+2)) (8*(11920000+1500000+16008100*A+37)) n) :
    let ceiling := geometryGateCeiling (8*(11920000+1500000+16008100*A+37)) (4*(E+2)) r n
    let program := geometryTable top ord₀ (plan.profile_order_fits widths ord) target x
    let bits := BottomReports.BundleSort.markedDepth cells J
    SignedTableStartupAt (aux:=φ ∘ cube.table) (q:=char) cube b (cube.signedSiteProgram e) adv c adDeg factor n
      program.size (program.reserve ceiling).size ceiling (written+(2^bits+2^bits)) packetWidth desc := by
  subst r packetWidth
  subst digits tagCap
  have selected := inputs sitePos
  dsimp only at selected
  rw [← Nat.mul_assoc 6 (R+1) tiles, ← Nat.mul_assoc 4 (R+1) tiles] at selected
  obtain ⟨volume,room,_,_,hs₁,hf₁,_,_,_,wp,wd,wb,wh,wl⟩ := selected
  have keyRoom := room.2.1
  have logs := room.2.2.1
  have receipt := frozenPacketWithBundles_clock S G order position σ actual count cellNumber
    vf cf hg short extend dir number sitePos ownerFits arena stride gap desc gadgets (b.physical.word n) controls hs hf
    keyFits sitesFit keysFit sw pad dest hdr bankLayout shapes plan wr hm widths ord E A 37 hpos nv
    qpos paid keyRoom logs qFit wp wd wb wh wl volume controlsFit window x
  have wp₀ : 1 ≤ b.physical.word n := nv.symm ▸ Nat.pow_pos hpos
  intro ceiling program bits
  unfold SignedTableStartupAt
  intro r W R₁ ξ link₁ lit start sites T₁ entries reserve cap₁ input first free l size₁ order₁ common chart _ _ reader small
  exact install.startup cube _ _ _ _ x wp₀ desc receipt chart reader small

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
