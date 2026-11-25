import OAI.Hierarchy.DescentMountedHistoryCountReel
import OAI.Hierarchy.DescentLateReelPrice

namespace OAI
/-! Charge the terminal role mount once between count capture and the original early reel. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentExteriorMatrixUpdate DescentExteriorShelf DescentStaticWordColumn Chronology
open DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory DescentGL DescentColonies DescentExterior PinCohorts
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (S : AtomSchedule)
    (roof : ℕ) (tag : ℕ→Bool) (rotation loc : ℕ→ℕ) (lo compact k tail j r s w : ℕ)
    (mount : NativePhase w) (term : Procedure w) (termClocks : ℕ)
    (plan : Reel) (dim wall : ℕ)
local notation "E" => Fintype.card (Port P X.width)
local notation "dates" => countDates 0 (kindCalendar S.rounds S.height)
local notation "countTicks" => 4+11*(dates).length
local notation "earlyTicks" => Calendar.earlyClock S k tail j r s E
local notation "post" => Calendar.postProgram plan dim S.length j r s E w compact wall
local notation "old" => historyCountReel X S roof tag rotation loc lo compact k tail j r s w
local notation "newReel" => historyMountedReel X S roof tag rotation loc lo compact k tail j r s w mount
local notation "oldProgram" => ((old).seq term).seq post
local notation "newProgram" => (((newReel).seq term).seq (relocate j r s E w compact wall)).seq
  (plan.program j r s E w dim S.length wall)
local notation "oldCharge" => countTicks+earlyTicks+termClocks+Calendar.postClock S.length j r s E+7*names oldProgram
local notation "newCharge" => ((countTicks+mount.ticks)+earlyTicks)+termClocks+
  (4+18*(17*span j r s E))+(10+((4+58*S.length)+(4+16*E)))+7*names newProgram

omit [Field F] in
/-- Exact bit cost of the physical paid replay after inserting the terminal dictionary program. -/
theorem mounted_counted_post_identity (weight scale : ℕ) :
    newCharge*weight*scale=oldCharge*weight*scale+(mount.ticks+7*names mount.program)*weight*scale :=by
  simp only [historyCountReel,historyMountedReel,Calendar.postProgram,Calendar.postClock,names_seq]
  ring

omit [Field F] in
/-- Add the true complete original counted-reel invoice and the new single installation. -/
theorem mounted_counted_post_price (weight scale oldLimit mountLimit : ℕ)
    (original : oldCharge*weight*scale ≤ oldLimit)
    (installed : (mount.ticks+7*names mount.program)*weight*scale ≤ mountLimit) :
    newCharge*weight*scale ≤ oldLimit+mountLimit :=by
  rw [mounted_counted_post_identity X S roof tag rotation loc lo compact k tail j r s w mount term termClocks plan dim wall]
  exact Nat.add_le_add original installed

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
