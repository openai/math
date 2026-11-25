import OAI.Hierarchy.DescentCompleteBootReel
import OAI.Hierarchy.DescentObservedMountedBootReel

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
open DescentDatedSeedStartup DescentDatedSeedStartup.Input DescentSeedRoot DescentSeedInitialTable DescentPackedSeed DescentRotor DescentInitialHost
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

variable (op : RotorSpec) {hosts : ℕ} (wide : Fintype.card b.origin.raw.V≤hosts)
    (pub : Fintype.card (Vertex X)≤hosts) (l : DescentDatedSeedStartup.Layout) (header payload Z : ℕ)
local notation "ds" => S.initialDigits radix
local notation "ch" => DescentDatedSeedStartup.Input.nodeChart l k hosts (S.groupCount 0)
local notation "seedEnd" => (ch).seedEnd (DescentDatedSeedStartup.endAddress X l hosts (S.groupCount 0) k)
local notation "pitch" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "bound" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k hosts (S.groupCount 0) pitch seedEnd
local notation "boot" => completeAfter G op X ds pub l header payload Z
local notation "ticks" => completeTicks (S:=S) (k:=k) G op X pub l payload Z
local notation "startedAt" => completeImage G op X ds pub l header payload Z
include wide in
theorem booted_mounted_early_prefix {w : ℕ} (date : ℕ→DateCode w) (raw : Memory w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes≤w)
    («fields» : l.operandBits*l.operandLanes≤w) (earlyWord : header<l.base)
    (sourceSpace : DescentPackedSeed.publicWords X+DescentDyadicSpan.span jobs≤ seedEnd)
    (active : 0<pitch) (embed : payload≤w) (space : bound<2^w)
    (total : ∀i< S.length,∀m,∃out,(date i).Runs m out) (limit : ℕ) (accepted : Prop)
    (x : Fin E→Plane j rest→Fin t→Bool) (z : Hidden E j rest t→Bool)
    (printed : Loaded compact (fun _=>LinearEquiv.refl _ _) x z raw)
    (floors : ℕ→ℕ) (original : compact+17*H≤ header)
    (order : ∀i< S.length,header< floors i)
    (observed : b.path.dateReadbacks (DateCode.history date (startedAt raw)) tag rotation loc limit accepted)
    (apartCount : ∀i< S.length,loc i≠header) (apartMatrix : ∀i< S.length,rotation i≠header)
    (keepCount : ∀j< S.length,∀i,S.length≥i→ j< i→ loc j< floors i)
    (keepMatrix : ∀j< S.length,∀i,S.length≥i→ j< i→ rotation j< floors i)
    (frame : ∀i< S.length,∀a,a≠header→a< floors i→
      DateCode.history date (startedAt raw) (i+1) a=DateCode.history date (startedAt raw) i a)
    (batchFit : S.batch< 2^w)
    (lowWrite : lo+(dates).length≤ compact) (below : compact+32*H≤ roof)
    (locs : ∀a∈dates,lo+(dates).length≤ loc a ∧ loc a+1< 2^w)
    (rotLo : ∀a< S.length,lo+(dates).length≤ rotation a) (rotHi : ∀a< S.length,rotation a< roof)
    (word : Calendar.earlyEnd S k tail roof j rest t E< 2^w)
    (roleBase:ℕ) (mount:Chronology.RoleMount w roleBase roof) (preRole:compact+32*H≤roleBase)
    (rotRole:∀i<S.length,rotation i<roleBase) :
    let m:=DateCode.history date (startedAt raw) S.length
    let copied:=DescentLowCountBook.output lo source m (dates).length
    let out:=Calendar.earlyImage S k tail roof tag rotation j rest t E compact (mount.phase.image copied)
    ((DateCode.afterBoot (boot w) date S.length).seq
      (historyMountedReel X S roof tag rotation loc lo compact k tail j rest t w mount.phase)).Exec raw out
      (DateCode.afterTicks (ticks w) date S.length+(((4+11*(dates).length)+mount.phase.ticks)+Calendar.earlyClock S k tail j rest t E)) ∧
    (∀a,∀v,a< limit→b.path.selections[a]?=some v→(out (lo+a)).val=selectionCount G v) ∧
    (accepted→Loaded early (publicLayout X G S b hp base width) x z out ∧ b.path.savedRotations reel end_ tail out) :=by
  have seeded:=complete_after_count G op X ds pub l header payload Z b.origin wide raw signed «fields» earlyWord
    sourceSpace active embed space
  have loaded : Loaded compact (fun _=>LinearEquiv.refl _ _) x z (startedAt raw):=by
    intro col j hj
    have ci : col.val+1≤17:=col.isLt
    have before : compact+col.val*H+j<header:=by
      have mul:=Nat.mul_le_mul_right H ci
      rw [Nat.add_mul,one_mul] at mul
      omega
    change (startedAt raw) (compact+col.val*H+j)=_
    rw [seeded.2.2.2.2 _ before.ne (.inl (before.trans earlyWord))]
    exact printed col j hj
  exact observed_mounted_boot_reel X G S b hp base width roof tag rotation loc lo compact (boot w) (ticks w) date
    raw (startedAt raw) seeded.1 total limit accepted x z loaded floors header original order observed
    apartCount apartMatrix keepCount keepMatrix frame batchFit lowWrite below locs rotLo rotHi word roleBase mount preRole rotRole

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Branch.pinSpine Branch.publicSpine Branch.publicLayout
