import OAI.Hierarchy.DescentObservedBootReel
import OAI.Hierarchy.DescentMountedHistoryCountReel

namespace OAI
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
variable (width : S.groupWidth k tail 0+k=j+(j+rest))

variable {t : ℕ} (roof : ℕ) (tag : ℕ→Bool) (rotation : ℕ→ℕ)
local notation "end_" => Calendar.stop S k tail roof
local notation "early" => Calendar.earlyAt S k tail roof
local notation "reel" => Calendar.reel S k tail roof tag rotation
local notation "H" => span j rest t E

open Chronology DescentTerminalEpochDecoder
local notation "tags" => kindCalendar S.rounds S.height
local notation "dates" => countDates 0 tags
variable (loc : ℕ→ℕ) (lo compact : ℕ)
local notation "source" => (fun (j:ℕ)=>loc ((dates)[j]?.getD 0))

/-- The original immutable exterior bytes stay at their native addresses through all dated
writes, including private meter updates. -/
theorem observed_mounted_boot_reel {w : ℕ} (boot : Procedure w) (bootTicks : ℕ) (date : ℕ→DateCode w)
    (raw initial : Memory w) (started : boot.Exec raw initial bootTicks)
    (total : ∀i< S.length,∀m,∃out,(date i).Runs m out) (limit : ℕ) (accepted : Prop)
    (x : Fin E→Plane j rest→Fin t→Bool) (z : Hidden E j rest t→Bool)
    (printed : Loaded compact (fun _=>LinearEquiv.refl _ _) x z initial)
    (floors : ℕ→ℕ) (header : ℕ) (original : compact+17*H≤ header)
    (order : ∀i< S.length,header< floors i)
    (observed : b.path.dateReadbacks (DateCode.history date initial) tag rotation loc limit accepted)
    (apartCount : ∀i< S.length,loc i≠header) (apartMatrix : ∀i< S.length,rotation i≠header)
    (keepCount : ∀j< S.length,∀i,S.length≥i→ j< i→ loc j< floors i)
    (keepMatrix : ∀j< S.length,∀i,S.length≥i→ j< i→ rotation j< floors i)
    (frame : ∀i< S.length,∀a,a≠header→a< floors i→
      DateCode.history date initial (i+1) a=DateCode.history date initial i a)
    (batchFit : S.batch< 2^w)
    (lowWrite : lo+(dates).length≤ compact) (below : compact+32*H≤ roof)
    (locs : ∀a∈dates,lo+(dates).length≤ loc a ∧ loc a+1< 2^w)
    (rotLo : ∀a< S.length,lo+(dates).length≤ rotation a) (rotHi : ∀a< S.length,rotation a< roof)
    (word : Calendar.earlyEnd S k tail roof j rest t E< 2^w)
    (roleBase:ℕ) (mount:Chronology.RoleMount w roleBase roof) (preRole:compact+32*H≤roleBase)
    (rotRole:∀i<S.length,rotation i<roleBase) :
    let m:=DateCode.history date initial S.length
    let copied:=DescentLowCountBook.output lo source m (dates).length
    let out:=Calendar.earlyImage S k tail roof tag rotation j rest t E compact (mount.phase.image copied)
    ((DateCode.afterBoot boot date S.length).seq
      (historyMountedReel X S roof tag rotation loc lo compact k tail j rest t w mount.phase)).Exec raw out
      (DateCode.afterTicks bootTicks date S.length+(((4+11*(dates).length)+mount.phase.ticks)+Calendar.earlyClock S k tail j rest t E)) ∧
    (∀a,∀v,a< limit→b.path.selections[a]?=some v→(out (lo+a)).val=selectionCount G v) ∧
    (accepted→Loaded early (publicLayout X G S b hp base width) x z out ∧ b.path.savedRotations reel end_ tail out) :=by
  intro m copied out
  have native : (DateCode.afterBoot boot date S.length).Exec raw m (DateCode.afterTicks bootTicks date S.length) :=
    DateCode.boot_history boot bootTicks date raw initial started S.length total
  have input:=original_until (S:=S) (X:=X) compact (DateCode.history date initial)
    floors header x z printed original order frame
  obtain ⟨n,matrix⟩:=b.path.retained_words (DateCode.history date initial) tag rotation loc limit accepted
    observed floors header apartCount apartMatrix keepCount keepMatrix frame radix le_rfl batchFit
  obtain ⟨ran,counts,rotations,_⟩:=mounted_counted_reel X G S b hp base width roof tag rotation loc lo compact
    m limit accepted x z input n matrix lowWrite below locs rotLo rotHi word roleBase mount preRole rotRole
  exact ⟨Procedure.Exec.then native ran,counts,rotations⟩

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Branch.pinSpine Branch.publicSpine Branch.publicLayout
