import OAI.Hierarchy.TaggedWideFundedLocal
import OAI.Hierarchy.TaggedWideFundedGateRoom
import OAI.Hierarchy.TaggedWideWindowProgramLayout
import OAI.Hierarchy.TaggedWideCalendarAssemblyCore

namespace OAI
/-! # Observations of the purchased windows inside a larger paid memory -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard PhysicalTerm ReportSockets Tagged TaggedShorterBudget
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune
open ProtocolRAMFrozenWindow TaggedShorterSupergroups WideStack WideControlJoin WideCalendarSites
open scoped Classical BigOperators
set_option quotPrecheck false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ : ℝ} {u : ℝ → ℝ}
variable (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A)
  (m ell short bits cap : ℕ) (dated : WideCPU.Dated (events v.mesh).length) (romStart : ℕ)
local notation "layout" => v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart
local notation "menu" => v.wideWindowMenu m ell short u δ ξ
local notation "geometry" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _ => short+ell)
local notation "dir" => WideMemory.dir x.h v.W k v.wideJobs
local notation "ports" => WideMemory.H x.h v.W k v.wideJobs
local notation "slots" => purchaseSlots x.h v.W k v.wideJobs ell
local notation "counts" => purchaseModules v.W u δ ξ menu x
local notation "candidates" => fun i : Fin (m+1) => purchaseCandidates x.h v.W k v.wideJobs slots ((menu).height i x) (counts i)

variable {X : Type} {d R M den : ℕ} {eventPin : Event → WireTelescope.CalendarTape.Slot X} {es : List Event}
    {state : Equiv.Perm (Row x.h) → X}
    (Z : CalendarTerms F x.h d k x.w R M den eventPin es state)
    {E H : Type} [Fintype E] [Fintype H] (capT : E → ℕ) (histCap : H → ℕ) (dates view : ℕ)
local notation "D" => CalendarTerms.Shared (geometry).index capT histCap (dir).groups ports (2^ell) dates view x.w
local notation "rout" => Z.nativeRouting D
local notation "ext" => OpenPins x.h x.w (rout).catalyst
local notation "sel" => Fin (rout).selectors
local notation "sites" => Fin (siteLast x.h d k+1)
variable (first paid : Gate)
local notation "V" => SitePins ext sel D paid

include Z capT histCap dates view first paid in
/-- Read each original window in its installed part of the paid machine's
observation array, allowing that array to extend past the pruning pass. -/
def wideWindowLocalProgramsAt
    (head : first.Head → (ext⊕sel)⊕Bool) (paidHead : paid.Head → (ext⊕sel)⊕Bool)
    (flag : Fin first.u) (keep pad privateGate plane timeline : Net F V)
    (enter finish : sites → Net F V) (row : sites → Fin es.length → Net F V)
    (upper : (layout).pruneScratch+(layout).pruneRows+1 ≤ paid.u)
    (bitsOK : Native.wordBits x.h (2^v.W) Native.copies ≤ paid.W)
    (large : purchaseWordHeight v.W k v.wideJobs ell ≤ x.h) :
    LocalPrograms (F:=F) (k:=k) (M:=M) x («menu»:=menu) (fun _ => slots) candidates :=
  fundedLocalPrograms v.W m v.wideJobs ell short v.stage_positive x Z capT histCap dates view
    first paid head paidHead flag keep pad privateGate plane timeline enter finish row
    (fun i => ((layout).windows i).window.base ((layout).windowBase i))
    (fun i => by
      apply (((layout).windows i).scatter_end ((layout).windowBase i)).trans
      have inside : ((layout).windows i).window.stop ((layout).windowBase i) ≤
          WindowSeries.finish (layout).floor (layout).need := by
        rw [Size.stop_add]
        exact WindowSeries.within (layout).floor (layout).need i
      have endAt : WindowSeries.finish (layout).floor (layout).need=(layout).pruneScratch := rfl
      rw [endAt] at inside
      exact inside.trans ((Nat.le_add_right (layout).pruneScratch ((layout).pruneRows+1)).trans
        (by simpa only [Nat.add_assoc] using upper)))
    (fun i => (purchase_word_fit (u:=u) (δ:=δ) (ξ:=ξ) v.W m k v.wideJobs ell short
      v.stage_positive x large i).trans bitsOK)

variable {C : ℝ}

include Z capT histCap dates view first paid in
/-- The native frame places the same actual purchased cuts in the calendar
network and uses the chosen gate's own admission flag. -/
theorem wideWindowLocalProgramsAt_compile
    (head : first.Head → (ext⊕sel)⊕Bool) (paidHead : paid.Head → (ext⊕sel)⊕Bool)
    (flag : Fin first.u) (keep pad privateGate plane timeline : Net F V)
    (enter finish : sites → Net F V) (row : sites → Fin es.length → Net F V)
    (upper : (layout).pruneScratch+(layout).pruneRows+1 ≤ paid.u)
    (bitsOK : Native.wordBits x.h (2^v.W) Native.copies ≤ paid.W)
    (large : purchaseWordHeight v.W k v.wideJobs ell ≤ x.h)
    (items : PurchaseList (F:=F) (C:=C) menu x (fun _ => slots) candidates counts) :
    let core := v.wideWindowLocalProgramsAt x m ell short bits cap dated romStart
      Z capT histCap dates view first paid head paidHead flag keep pad privateGate plane timeline
      enter finish row upper bitsOK large
    (core).compile menu x (fun _ => slots) candidates counts items =
      Z.assembled (geometry).index capT histCap (dir).groups ports (2^ell) dates view
        first paid head paidHead flag keep pad privateGate plane timeline enter finish row
        (fun i => (items i).cut ((core).read i)) (fun i => ⌊((menu).height i x:ℝ)^A⌋₊) := rfl


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
