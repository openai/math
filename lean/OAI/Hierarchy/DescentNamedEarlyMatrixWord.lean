import OAI.Hierarchy.DescentNamedEarlyRotation

namespace OAI
/-! The last matrix is available directly at its dated scalar register for every number of exterior ports. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory DescentGL DescentColonies DescentExterior
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
attribute [local irreducible] Origin.source
set_option quotPrecheck false
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

namespace Branch
open PinCohorts DescentExteriorMatrixUpdate DescentExteriorShelf
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "shape" => j+(j+rest)
local notation "E" => Fintype.card (Port P X.width)
variable (width : S.groupWidth k tail 0 + k = j + (j + rest))

variable {t : ℕ} (roof : ℕ) (tag : ℕ→Bool) (rotation : ℕ→ℕ)
local notation "end_" => Calendar.stop S k tail roof
local notation "early" => Calendar.earlyAt S k tail roof
local notation "reel" => Calendar.reel S k tail roof tag rotation
local notation "H" => span j rest t E


/-- The first terminal matrix broadcast preserves its source. In particular the cumulative
register remains meaningful when the broadcast itself has no destination ports. -/
theorem early_matrix_word {bw : ℕ} (compact : ℕ) (m : Memory bw)
    (held : b.path.RotationWords tag rotation m) (rotationLow : ∀i<S.length,rotation i<roof)
    (before : compact+32*H≤roof) (word : Calendar.earlyEnd S k tail roof j rest t E<2^bw) :
    Calendar.earlyImage S k tail roof tag rotation j rest t E compact m (end_+S.length)=
      ((matrixCode (Branch.pinSpine X G S b hp base).matrix).val:Computability.VPVNP.BurstRAM.Word bw) := by
  have start : roof≤end_:=Nat.le_add_right ..
  have next : end_<early:=by change end_<end_+S.length+1;omega
  have mass : 0<H:=Nat.two_pow_pos _
  have fits : early+17*H<2^bw:=(Nat.add_le_add_left (Nat.le_max_left ..) _).trans_lt word
  have total : end_+S.length+2<2^bw:=by change end_+S.length+1+17*H<2^bw at fits;omega
  let rom:=Calendar.sheet S k tail roof tag bw
  let pre:=rom.output m
  let middle:=relocated j rest t E compact early pre
  obtain ⟨_,dates,_⟩:=b.path.issue_rotations tag rotation roof m held base rotationLow le_rfl total
  obtain ⟨_,_,_,safe⟩:=relocate_run (j:=j) (r:=rest) (t:=t) (e:=E) compact early pre
    (before.trans (start.trans next.le)) fits
  have saved:=b.path.savedRotations_move reel end_ dates (fun a low=>safe a (.inl (low.trans next)))
  have geom:=Calendar.room S k tail roof tag rotation rotationLow total
  let prior:=initialized ((reel).old 0) initialBits middle
  have boot:=«initialize» ((reel).old 0) initialBits middle geom.startFit
  have kept : b.path.savedRotations reel end_ tail prior:=
    b.path.savedRotations_move reel end_ saved (fun a ha=>boot.2.2.2 a (by have:=geom.boot;omega))
  have physical:=b.path.matrixInputs_of_saved reel end_ base radix p hp _ b.origin.particles
    b.recorded prior kept geom.retained
  have initial : prior (((reel).cells initialBits 0).old.base)=
      ((matrixCode (Spine.start (active b.origin.source base radix) (host b.origin.source)).matrix).val:Computability.VPVNP.BurstRAM.Word bw):=by
    change initialized ((reel).old 0) initialBits middle ((reel).old 0) = _
    simpa only [initialCode_eq (active b.origin.source base radix) (host b.origin.source)] using boot.2.2.1
  have read:=b.path.matrix_read base radix p hp _ _ b.recorded ((reel).cells initialBits) prior
    physical initial geom.join
  let reached_:=DescentExteriorMatrixUpdate.reached ((reel).cells initialBits) prior S.length
  change ProtocolRAM.image (early+H) E (broadcast (end_+S.length)) reached_ (end_+S.length)=_
  have outside : end_+S.length<early+H:=by change _<end_+S.length+1+H;omega
  rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl outside)]
  exact read

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Branch.pinSpine Branch.publicSpine Branch.publicLayout
