import OAI.Hierarchy.DescentNamedEarlyRotation
import OAI.Hierarchy.DescentChronologicalWordReads

namespace OAI
/-! # The observed count tape and early cumulative matrix in the very same public RAM -/
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

def historyCountReel (k tail j rest t : ℕ) (w : ℕ) :=
  (DescentLowCountBook.program w lo source (dates).length).seq
    (Calendar.earlyProgram S k tail roof tag rotation j rest t E compact w)

theorem counted_reel {w : ℕ} (m : Memory w) (limit : ℕ) (accepted : Prop)
    (x : Fin E→Plane j rest→Fin t→Bool) (z : Hidden E j rest t→Bool)
    (printed : Loaded compact (fun _=>LinearEquiv.refl _ _) x z m)
    (occurs : b.path.CountsAt loc limit m) (words : accepted→b.path.RotationWords tag rotation m)
    (lowWrite : lo+(dates).length≤compact) (below : compact+32*H≤roof)
    (locs : ∀a∈dates,lo+(dates).length≤loc a ∧ loc a+1<2^w)
    (rotLo : ∀a<S.length,lo+(dates).length≤rotation a) (rotHi : ∀a<S.length,rotation a<roof)
    (word : Calendar.earlyEnd S k tail roof j rest t E<2^w) :
    let copied:=DescentLowCountBook.output lo source m (dates).length
    let out:=Calendar.earlyImage S k tail roof tag rotation j rest t E compact copied
    (historyCountReel X S roof tag rotation loc lo compact k tail j rest t w).Exec m out
      ((4+11*(dates).length)+Calendar.earlyClock S k tail j rest t E) ∧
    (∀a,∀v,a<limit→b.path.selections[a]?=some v→(out (lo+a)).val=selectionCount G v) ∧
    (accepted→Loaded early (publicLayout X G S b hp base width) x z out ∧ b.path.savedRotations reel end_ tail out) ∧
    ∀a,(a<lo ∨ lo+(dates).length≤a)→
      (a<roof ∨ Calendar.earlyEnd S k tail roof j rest t E≤a)→ out a=m a :=by
  intro copied out
  have normalized : (dates).length=b.path.selections.length:=by
    exact (congrArg (fun kinds : List Bool => (countDates 0 kinds).length) b.kinds.symm).trans b.path.countDates_length
  have meet : roof≤Calendar.earlyEnd S k tail roof j rest t E:=by
    change roof≤(roof+S.length*Calendar.stride S k tail+S.length+1)+_
    omega
  have oldFits : lo<2^w:=(show lo≤roof by omega).trans_lt (meet.trans_lt word)
  have addr (i : ℕ) (hi : i<(dates).length) : source i=(loc (dates)[i]):=by
    simp only [List.getElem?_eq_getElem hi,Option.getD_some]
  have doCopy : (DescentLowCountBook.program w lo source (dates).length).Exec m copied (4+11*(dates).length):=DescentLowCountBook.run lo source m (dates).length oldFits
    (fun i hi => (Nat.add_le_add_left hi.le lo).trans
      (le_trans (locs _ (List.getElem_mem hi)).1 (addr i hi).symm.le))
    (fun i hi => (Nat.add_le_add_right (addr i hi).le 1).trans_lt (locs _ (List.getElem_mem hi)).2)
  have oldR := Calendar.early_run S k tail roof tag rotation j rest t E compact copied
    (by
      cases w with
      | zero =>
        simp only [pow_zero] at word
        have mass : 0 < H := Nat.two_pow_pos _
        omega
      | succ w => exact Nat.succ_pos _) rotHi below word
  have counts:=b.path.copy_counts loc limit lo m occurs tags b.kinds
    (fun a inside=>by rw [←normalized];exact (locs a inside).1)
  refine ⟨?_,?_,?_,?_⟩
  · exact Procedure.Exec.then doCopy oldR.1
  · intro a v used found
    have valid : a<(dates).length:=by
      rw [normalized];by_contra! impossible
      rw [List.getElem?_eq_none impossible] at found;contradiction
    exact (congrArg Fin.val (oldR.2.2 (lo+a) (.inl (by omega)))).trans (counts a used v found)
  · intro good
    have image : Loaded compact (fun _=>LinearEquiv.refl _ _) x z copied:=by
      intro col i hi
      have large : lo+(dates).length≤(bank j rest t E compact col.val).base+i:=by
        change _≤compact+col.val*H+i;omega
      exact (DescentLowCountBook.frame lo source m (dates).length _ (.inr large)).trans (printed col i hi)
    have moved:=Path.RotationWords.move b.path tag rotation (words good) (fun a ha=>
      DescentLowCountBook.frame lo source m (dates).length _ (.inr (rotLo a ha)))
    exact early_exterior X G S b hp base width roof tag rotation compact copied x z image moved rotHi below word
  · intro a separate banks
    exact (oldR.2.2 _ banks).trans (DescentLowCountBook.frame lo source m (dates).length _ separate)

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Branch.pinSpine Branch.publicSpine Branch.publicLayout
