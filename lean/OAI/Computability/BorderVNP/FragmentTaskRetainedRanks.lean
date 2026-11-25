import OAI.Computability.BorderVNP.FragmentTaskPublishedRanks
import OAI.Computability.BorderVNP.PackedTerminalRetainedReturn
import OAI.Computability.BorderVNP.CubeRouteProfileControls
import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedReportSeed

/-! # Task marker ranks on the native geometry and control returns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained

open CellPacketGeometry CellPacketGeometry.LiveWords ParseBatchSort VPVNP.VerifierNetwork
open Packing Packing.CellAddressCircuit GeometryFrameEncoding
open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM RoutingISA.SignedTaskArena

variable {X Y V Z H E I Orig Pins : Type} [Fintype X] [Fintype Y] [Fintype V] [Fintype Z] [Fintype H]
    [Fintype E] [Fintype I] [Fintype Pins]
variable {s m n C d k w J P W active reserve v sites cells q : ℕ}
    (F : Fields s m n C d k w (Z ⊕ Bool)) (hk : k ≤ w) (old : Fin J → Fin s) (ports : Fin P → Fin n)
    (controls : Fin v → Fin (2^w)) (sewn : Frame ((X ⊕ Fin reserve) ⊕ V) (Z ⊕ Bool))
    (keep : Frame ((X ⊕ Fin reserve) ⊕ V) H) (hist : Frame (X ⊕ Y) (V ⊕ Unit))
    (ord : Y ≃ Fin active) (fit : active ≤ reserve) (x : X → Bool) (word : Fin reserve → Bool)
variable (T : Template E I Orig sites cells) (up : Frame Pins (Base sites k w E I))
    (anchors : Frame Pins (Fin sites × Fin q)) (baseOwner : Fin sites → Fin cells) (pin : Orig → T.Fields)
    (pad : sites < 2^q) (feed : Frame ((Z ⊕ Bool) ⊕ H) Pins) (hdr preceding bundleBits : ℕ)
variable {pub : Arg → Word W} {mac : TeamOpcode.Macros W 8} {reg after : RoutingISA.Bank W} {mem result : Memory W}
    {fresh dest clock : ℕ} {es : List (TeamRAM.Event W)}
local notation3 "wordBase" => packetBase dest m C J P v
local notation3 "packet" => (T.orderedFrame up anchors baseOwner pin pad wordBase hdr).subst feed

/-- The actual native return of the joined terminal emitter supplies the
numeric task bounds at the published descriptor inverse addresses. The
word-sorted and descriptor-sorted banks occupy different ranges in that
one physical output. -/
theorem packet_return_taskRanks (width : w≤W) (wide : 2^T.chunkDepth ≤ 2^w)
    (run : GeometryReturn pub mac reg mem fresh dest clock
      (emittedWords hist ord fit (emitter F hk old ports (privateControls F old controls packet) sewn keep) x word)
      es after result) :
    (GeometryDirectories.published wordBase T.publicDepth T.chunkDepth cells T.chunkLabels.length
      (RoutingOutputs.controlsBase dest m C J P) preceding bundleBits).MarkerBounds cells (readings result) := by
  let input := branch hist ord fit x word
  let words := (packet_return hk old ports keep hist ord fit x word F controls packet sewn width run).2
  apply T.publishedTaskRanks up anchors baseOwner pin pad wordBase hdr _ preceding bundleBits
    (feed.eval (Sum.elim (sewn.eval input) (keep.eval input))) wide
  intro i
  exact (words i).trans (congrArg value (funext fun j => Frame.subst_eval ..))

/-- The saved index and advice words end before both the 37-word controller
and the actual inverse descriptor bank written by this terminal emitter. -/
theorem packet_reader_floor (floor fresh profile gates words digit m C J P controls p d cells chunks preceding bundleBits : ℕ)
    (before : floor ≤ fresh) :
    let origin := GeometryAdvice.Allocation.dest fresh profile gates words digit
    let ctl := RoutingOutputs.controlsBase origin m C J P
    let dir := GeometryDirectories.published (packetBase origin m C J P controls) p d cells chunks ctl preceding bundleBits
    floor ≤ ctl ∧ floor ≤ dir.sorted := by
  intro origin ctl dir
  have freshOutput : fresh ≤ origin := by dsimp only [origin,GeometryAdvice.Allocation.dest,GeometryAdvice.Allocation.temp]; omega
  have controlsAfter : origin ≤ ctl := by dsimp only [ctl,RoutingOutputs.controlsBase,RoutingOutputs.bases]; omega
  have low := before.trans (freshOutput.trans controlsAfter)
  exact ⟨low, (low.trans (Nat.le_add_right ctl controls)).trans (Nat.le_add_right _ (2^p+2^p))⟩

/-- The native output count places the entire descriptor inverse array after
the controller and before the cube header at the end of reconstruction. -/
theorem packet_descriptor_room {fresh profile gates words digit W m C J P controls p d : ℕ}
    (head geomCells chunks preceding bundleBits : ℕ) (frame : head+112 ≤ fresh) (fixed : 37 ≤ controls)
    (emitted : m*3+(RoutingOutputs.count m C J P+((C+(J+C))+(controls+Total p d))) ≤ words) :
    let origin := GeometryAdvice.Allocation.dest fresh profile gates words digit
    let ctl := RoutingOutputs.controlsBase origin m C J P
    let dir := GeometryDirectories.published (packetBase origin m C J P controls) p d geomCells chunks ctl preceding bundleBits
    head+112 ≤ dir.sorted ∧ ctl+37 ≤ dir.sorted ∧ dir.sorted+2*dir.padded ≤ GeometryAdvice.Allocation.stop fresh profile gates words digit W := by
  intro origin ctl dir
  have first : fresh ≤ origin := by dsimp only [origin,GeometryAdvice.Allocation.dest,GeometryAdvice.Allocation.temp]; omega
  have originCtl : origin ≤ ctl := by
    dsimp only [ctl,RoutingOutputs.controlsBase,RoutingOutputs.bases]
    omega
  have afterCtl : ctl+37 ≤ dir.sorted := by
    change ctl+37 ≤ ctl+controls+(2^p+2^p)
    exact (Nat.add_le_add_left fixed ctl).trans (Nat.le_add_right ..)
  refine ⟨frame.trans (first.trans (originCtl.trans ((Nat.le_add_right ..).trans afterCtl))),afterCtl,?_⟩
  have finish : dir.sorted+2*dir.padded = origin+
      (m*3+(RoutingOutputs.count m C J P+((C+(J+C))+(controls+Total p d)))) := by
    dsimp only [dir,GeometryDirectories.published,packetBase,descriptorBank,ctl,RoutingOutputs.controlsBase,
      RoutingOutputs.bases,RoutingOutputs.count,Total]
    ring
  rw [finish]
  apply (Nat.add_le_add_left emitted origin).trans
  change origin+words ≤ origin+words+_+_
  exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)

end PackedHistoryCircuit.Retained

namespace RoutingISA.SignedTaskArena

open FiniteEvaluator VPVNP.BurstRAM Packing

/-- The actual private-slot writes and the compacted seven-word demand rows
preserve the inverse bank, which follows all original and live pair slots. -/
theorem GeometryDirectories.MarkerBounds.after_directory {g : GeometryDirectories} {cells width frame origin edges C next gap : ℕ}
    (D : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) {profile placed : Memory width}
    (ranks : g.MarkerBounds cells (readings profile))
    (slots : (RoutingOutputs.privateLayout frame origin edges C D.entries D.description gap).Image
      (readings profile) D.entries (readings placed))
    (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin)
    (before : RoutingOutputs.controlsBase origin edges C D.entries (D.teams*D.sites) ≤ g.sorted) :
    g.MarkerBounds cells (readings (Directory.ISA.publish placed frame next (D.directory pp lp))) := by
  let ctl := RoutingOutputs.controlsBase origin edges C D.entries (D.teams*D.sites)
  change ctl ≤ g.sorted at before
  have used := Nat.mul_le_mul_left 7 (D.directory_length_le pp lp)
  apply ranks.retained le_rfl
  intro a lower _
  have addr : a = ctl+(a-ctl) := by omega
  rw [addr]
  exact congrArg Fin.val (PackedHistoryCircuit.directoryPublished_control (live := D.teams*D.sites)
    (D.directory pp lp) slots low (by omega) (a-ctl))

variable {g : GeometryDirectories} {cells count w : ℕ} (t : Layout)
    {team frame offsets ctl live ports bundles b : ℕ} (owner : Fin bundles → Fin t.cube.cells)
    (header : Fin bundles → BottomReports.BundleHeader)
local notation3 "opening" => t.openInputs team frame offsets ctl live ports bundles b owner header

/-- Ownership, host scatter, the compact bundle writer and the actual cell
control writer preserve the earlier inverse descriptor rank columns. -/
theorem Layout.open_return_markerBounds {initial written : ℕ → ℕ} {input output : Memory w}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {regs endRegs : Bank w} {es : List (TeamRAM.Event w)}
    (base : (pub 0).val=frame)
    (retention : CubeAllocation.HostRetention t.cube frame initial written (readings input))
    (place : OpenSuffix.Placement opening t.cube t.before frame (readings input))
    (ready : OpenSuffix.Ready opening frame (readings input) w)
    (run : Runs pub mac OpenSuffix.code regs input es endRegs output)
    (ranks : g.MarkerBounds cells initial) (size : count ≤ cells)
    (lo : frame+112 ≤ g.sorted+g.padded) (hi : g.sorted+2*g.padded ≤ t.cube.header.header) :
    g.MarkerBounds count (readings output) := by
  have real : OpenSuffix.Ready opening (pub 0).val (readings input) w := base ▸ ready
  have image := ((OpenSuffix.run opening real).sound run).2
  change readings output= (opening).image (pub 0).val (readings input) at image
  have upper := t.open_table_order.1
  apply ranks.retained size
  intro a low high
  rw [image,base,t.open_image_low owner header place a (by omega) (by omega)]
  exact retention.lower a (high.trans_le hi) (by omega) (by omega)

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
