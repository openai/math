import OAI.Hierarchy.DescentMountedCountWords
import OAI.Hierarchy.DescentMountedExteriorInputs
import OAI.Hierarchy.DescentNamedCountedReel

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

def historyMountedReel (k tail j rest t : ℕ) (w : ℕ) (mount : NativePhase w) :=
  ((DescentLowCountBook.program w lo source (dates).length).seq mount.program).seq
    (Calendar.earlyProgram S k tail roof tag rotation j rest t E compact w)

theorem mounted_counted_reel {w : ℕ} (m : Memory w) (limit : ℕ) (accepted : Prop)
    (x : Fin E→Plane j rest→Fin t→Bool) (z : Hidden E j rest t→Bool)
    (printed : Loaded compact (fun _=>LinearEquiv.refl _ _) x z m)
    (occurs : b.path.CountsAt loc limit m) (words : accepted→b.path.RotationWords tag rotation m)
    (lowWrite : lo+(dates).length≤compact) (below : compact+32*H≤roof)
    (locs : ∀a∈dates,lo+(dates).length≤loc a ∧ loc a+1<2^w)
    (rotLo : ∀a<S.length,lo+(dates).length≤rotation a) (rotHi : ∀a<S.length,rotation a<roof)
    (word : Calendar.earlyEnd S k tail roof j rest t E<2^w)
    (roleBase : ℕ) (mount : RoleMount w roleBase roof) (preRole:compact+32*H≤roleBase)
    (rotRole:∀i<S.length,rotation i<roleBase) :
    let copied:=DescentLowCountBook.output lo source m (dates).length
    let staged:=mount.phase.image copied
    let out:=Calendar.earlyImage S k tail roof tag rotation j rest t E compact staged
    (historyMountedReel X S roof tag rotation loc lo compact k tail j rest t w mount.phase).Exec m out
      (((4+11*(dates).length)+mount.phase.ticks)+Calendar.earlyClock S k tail j rest t E) ∧
    (∀a,∀v,a<limit→b.path.selections[a]?=some v→(out (lo+a)).val=selectionCount G v) ∧
    (accepted→Loaded early (publicLayout X G S b hp base width) x z out ∧ b.path.savedRotations reel end_ tail out) ∧
    ∀a,(a<lo ∨ lo+(dates).length≤a)→
      (a<roleBase ∨ Calendar.earlyEnd S k tail roof j rest t E≤a)→ out a=m a :=by
  intro copied staged out
  have normalized : (dates).length=b.path.selections.length:=by
    exact (congrArg (fun kinds : List Bool => (countDates 0 kinds).length) b.kinds.symm).trans b.path.countDates_length
  have meet : roof≤Calendar.earlyEnd S k tail roof j rest t E:=by
    change roof≤(roof+S.length*Calendar.stride S k tail+S.length+1)+_
    omega
  have oldFits : lo<2^w:=(show lo≤roof by omega).trans_lt (meet.trans_lt word)
  have addr (i : ℕ) (hi : i<(dates).length) : source i=(loc (dates)[i]):=by
    simp only [List.getElem?_eq_getElem hi,Option.getD_some]
  have above (i:ℕ) (hi:i<(dates).length) : lo+i ≤ source i:=by
    exact (Nat.add_le_add_left hi.le lo).trans ((locs _ (List.getElem_mem hi)).1.trans (addr i hi).symm.le)
  have srcRoom (i:ℕ) (hi:i<(dates).length) : source i+1<2^w:=by
    exact (Nat.add_le_add_right (addr i hi).le 1).trans_lt (locs _ (List.getElem_mem hi)).2
  have bus : 0 < w := by
    cases w with
    | zero =>
      simp only [pow_zero] at word
      have mass : 0 < H := Nat.two_pow_pos _
      omega
    | succ w => exact Nat.succ_pos _
  have combined:=mounted_replay_run S k tail roof tag rotation j rest t E compact mount lo (dates).length source m
    bus oldFits above srcRoom rotHi below word
  have sourceHigh (a:ℕ) (inside:a<(dates).length) : lo + (dates).length ≤ source a := by
    exact (locs _ (List.getElem_mem inside)).1.trans (addr a inside).symm.le
  refine ⟨?_,?_,?_,?_⟩
  · exact combined.1
  · intro a v used found
    have valid : a<(dates).length:=by
      rw [normalized];by_contra! impossible
      rw [List.getElem?_eq_none impossible] at found;contradiction
    have read := mounted_count_word S k tail roof tag rotation j rest t E compact mount lo
      (dates).length source m sourceHigh (by omega) bus rotHi below word ⟨a, valid⟩
    change out (lo+a)=m (source a) at read
    rw [read, addr a valid]
    apply occurs a used v found
    rw [b.kinds]
    exact List.getElem?_eq_getElem valid
  · intro good
    have image : Loaded compact (fun _=>LinearEquiv.refl _ _) x z staged :=
      mount.loaded_after_counts lo (dates).length source m printed lowWrite (by omega)
    have moved:=Path.RotationWords.move b.path tag rotation (words good) (fun a ha=>
      mount.between_counts_and_tables lo (dates).length source m (rotLo a ha) (rotRole a ha))
    exact early_exterior X G S b hp base width roof tag rotation compact staged x z image moved rotHi below word
  · exact combined.2.2

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Branch.pinSpine Branch.publicSpine Branch.publicLayout
