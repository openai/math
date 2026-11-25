import OAI.Hierarchy.DescentExteriorPrime
import OAI.Hierarchy.DescentExteriorSelectedPublication

namespace OAI
/-! # Physical exterior words from all and only the selected local rotation receipts -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory DescentGL DescentColonies DescentExterior
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
set_option quotPrecheck false
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height (initialGroup X S.copies (S.firstWidth G.b p))}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p)

namespace NativeBranch
open PinCohorts DescentExteriorMatrixUpdate DescentExteriorShelf
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "E" => Fintype.card (Port P X.width)
variable (width : S.groupWidth k tail 0 + k = j + (j + rest))


/-- The selected local ordinary and reset codes determine the physical terminal shelf.
All other fields of the cumulative scan are the publicly computed calendar and its literal start. -/
theorem reel_layout {t bw : ℕ} (origin fence : ℕ) (plan : Reel) (m : Memory bw)
    (x : Fin E→Plane j rest→Fin t→Bool) (z : Hidden E j rest t→Bool)
    (printed : Loaded origin (fun _=>LinearEquiv.refl _ _) x z m)
    (entries : b.path.savedRotations plan fence tail m)
    (geometry : plan.Room bw initialBits S.length fence origin) :
    Loaded origin (publicLayout X G S b hp base width) x z
      (plan.result j rest t E initialBits S.length origin m) := by
  let prior:=initialized (plan.old 0) initialBits m
  have boot:=«initialize» (plan.old 0) initialBits m geometry.startFit
  have held : b.path.savedRotations plan fence tail prior:=
    b.path.savedRotations_move plan fence entries (fun a ha=>boot.2.2.2 a (by have:=geometry.boot;omega))
  have physical:=b.path.matrixInputs_of_saved plan fence base radix p hp _
    (Chronology.seed_particles X (Chronology.epochsSource G r c) b.source (S.initialDigits radix) b.seed)
    b.recorded prior held geometry.retained
  apply published_layout X G S b hp base width origin (plan.cells initialBits) prior x z _ geometry.high physical _ geometry.join
  · intro col u live
    have neq : plan.old 0 ≠ (bank j rest t E origin col.val).base+u:=by
      change plan.old 0 ≠ origin+col.val*span j rest t E+u
      have :=geometry.startLow
      omega
    exact (boot.2.2.2 _ neq).trans (printed col u live)
  · change initialized (plan.old 0) initialBits m (plan.old 0)=_
    simpa only [initialCode_eq (active b.source base radix) (host b.source)] using boot.2.2.1

end NativeBranch
end
end Hierarchy.DescentSixParty

end OAI
