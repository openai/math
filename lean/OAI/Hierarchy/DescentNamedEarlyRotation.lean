import OAI.Hierarchy.DescentNamedExteriorPublication
import OAI.Hierarchy.DescentEarlyRotationReel
import OAI.Hierarchy.DescentExteriorRelocatedContents

namespace OAI
/-! # Early native matrix at the authentic terminal cohort input -/
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

theorem early_exterior {bw : ℕ} (compact : ℕ) (m : Memory bw)
    (x : Fin E→Plane j rest→Fin t→Bool) (z : Hidden E j rest t→Bool)
    (printed : Loaded compact (fun _=>LinearEquiv.refl _ _) x z m)
    (held : b.path.RotationWords tag rotation m) (rotationLow : ∀i<S.length,rotation i<roof)
    (before : compact+32*H≤roof) (word : Calendar.earlyEnd S k tail roof j rest t E<2^bw) :
    let out:=Calendar.earlyImage S k tail roof tag rotation j rest t E compact m
    Loaded early (publicLayout X G S b hp base width) x z out ∧
    b.path.savedRotations reel end_ tail out :=by
  intro out
  have start : roof≤end_:=Nat.le_add_right ..
  have next : end_<early:=by change end_<end_+S.length+1;omega
  have mass : 0<H:=Nat.two_pow_pos _
  have fits : early+17*H<2^bw:=(Nat.add_le_add_left (Nat.le_max_left ..) _).trans_lt word
  have total : end_+S.length+2<2^bw:=by change end_+S.length+1+17*H<2^bw at fits;omega
  let rom:=Calendar.sheet S k tail roof tag bw
  let pre:=rom.output m
  let mid:=relocated j rest t E compact early pre
  obtain ⟨_,dates,raw⟩:=b.path.issue_rotations tag rotation roof m held base rotationLow le_rfl total
  have separated := before.trans (start.trans next.le)
  have safe := (relocate_run (j:=j) (r:=rest) (t:=t) (e:=E) compact early pre separated fits).2.2.2
  have seen : Loaded early (fun _=>LinearEquiv.refl _ _) x z mid :=by
    apply relocated_loaded compact early _ x z pre separated fits
    intro col i hi
    have bounded : (bank j rest t E compact col.val).base+i<roof:=by
      change compact+col.val*H+i<roof
      have bound:=Nat.mul_le_mul_right H col.isLt
      rw [Nat.succ_mul] at bound
      omega
    exact (raw _ (.inl bounded)).trans (printed col i hi)
  have saved:=b.path.savedRotations_move reel end_ dates (fun a low=>safe a (.inl (low.trans next)))
  have geom:=Calendar.room S k tail roof tag rotation rotationLow total
  have room₂ : early+H+E<2^bw:=by
    rw [Nat.add_assoc]
    exact (Nat.add_le_add_left (Nat.le_max_right ..) _).trans_lt word
  have wide : 0 < bw := by
    cases bw with
    | zero =>
      simp only [pow_zero] at total
      omega
    | succ w => exact Nat.succ_pos w
  have run:=(reel).run (j:=j) (r:=rest) (t:=t) (e:=E) initialBits S.length end_ early mid
    geom wide room₂
  exact ⟨reel_layout X G S b hp base width early end_ reel mid x z seen saved geom,
    b.path.savedRotations_move reel end_ saved run.2.2⟩

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Branch.pinSpine Branch.publicSpine Branch.publicLayout
