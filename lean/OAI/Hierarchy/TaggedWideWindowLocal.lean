import OAI.Hierarchy.TaggedWideWindowLayout
import OAI.Hierarchy.TaggedWideFundedLocal
import OAI.Hierarchy.TaggedWideCalendarAssembly
import OAI.Hierarchy.TaggedWidePrograms
import OAI.Hierarchy.TaggedWideFundedGateRoom
import OAI.Hierarchy.TaggedWideWindowProgramLayout

namespace OAI
/-! # Local purchased programs on the two actual signed calendar machines -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard PhysicalTerm ReportSockets Tagged TaggedShorterBudget
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune
open ProtocolRAMFrozenWindow TaggedShorterSupergroups WideStack WideControlJoin WideCalendarSites
open scoped Classical BigOperators
set_option quotPrecheck false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ : ℝ} {u : ℝ→ℝ}
variable (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (m ell short bits : ℕ)
variable (broadcast rom size : ℕ) (l : WideCPU.Layout m)
    (lim : v.GateRoom x.h x.w bits l size)
local notation "menu" => v.wideWindowMenu m ell short u δ ξ
local notation "geometry" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "fmt" => v.wideWindow x m ell short u δ ξ broadcast rom
local notation "dir" => WideMemory.dir x.h v.W k v.wideJobs
local notation "ports" => WideMemory.H x.h v.W k v.wideJobs
local notation "slots" => purchaseSlots x.h v.W k v.wideJobs ell
local notation "gates" => v.wideGates x.h x.w bits l size lim
local notation "U" => l.pruneScratch+l.pruneRows+1
variable (windows : l.windows = v.wideWindow x m ell short u δ ξ broadcast rom)
    (after : WindowSeries.finish l.floor l.need≤ l.pruneScratch)

include windows after in
/-- The terminal paid observation includes both physical subarrays for every menu class. -/
theorem wideWindow_observed (i : Fin (m+1)) : (fmt i).window.stop (l.windowBase i)≤ U := by
  have need : l.need = fun j=>(fmt j).window.stop 0 := funext fun j=>
    congrArg (fun f : Fin (m+1) → ProtocolRAMFrozenWindow.Format=>(f j).window.stop 0) windows
  have room := v.wideWindow_mutable_before x m ell short u δ ξ broadcast rom l.floor i
  change (fmt i).window.stop (WindowSeries.start l.floor l.need i)≤ _
  rw [need] at after ⊢
  exact room.trans (after.trans (by omega))

section Frame
variable {X : Type} {d R M den : ℕ} {eventPin : Event→ WireTelescope.CalendarTape.Slot X} {es : List Event}
    {state : Equiv.Perm (Row x.h)→ X}
    (Z : CalendarTerms F x.h d k x.w R M den eventPin es state)
    {E H : Type} [Fintype E] [Fintype H] (cap : E→ℕ) (historyCap : H→ℕ) (dates view : ℕ)
local notation "D" => CalendarTerms.Shared (geometry).index cap historyCap (dir).groups ports (2^ell) dates view x.w
local notation "rout" => Z.nativeRouting D
local notation "ext" => OpenPins x.h x.w (rout).catalyst
local notation "sel" => Fin (rout).selectors
local notation "sites" => Fin (siteLast x.h d k+1)
local notation "V" => SitePins ext sel D (gates).2

include lim windows after Z cap historyCap dates view in
/-- Both machine networks, flag zero and every purchased input use the fixed physical
calendar layout. The selected width class affects only the terminal assignment. -/
def wide_funded_local
    (head : (gates).1.Head → (ext⊕sel)⊕Bool) (paidHead : (gates).2.Head → (ext⊕sel)⊕Bool)
    (keep pad privateGate plane timeline : Net F V)
    (enter finish : sites → Net F V) (row : sites → Fin es.length → Net F V)
    (large : purchaseWordHeight v.W k v.wideJobs ell≤ x.h) :
    LocalPrograms (F:=F) (k:=k) (M:=M) x («menu»:=menu) (fun _=>slots)
      (fun i=>purchaseCandidates x.h v.W k v.wideJobs slots ((menu).height i x)
        (purchaseModules v.W u δ ξ menu x i)) :=
  fundedLocalPrograms v.W m v.wideJobs ell short v.stage_positive x Z cap historyCap dates view
    (gates).1 (gates).2 head paidHead (0 : Fin 1) keep pad privateGate plane timeline enter finish row
    (fun i=>(fmt i).window.base (l.windowBase i))
    (fun i=>((fmt i).scatter_end (l.windowBase i)).trans
      (v.wideWindow_observed x m ell short broadcast rom l windows after i))
    (fun i=>purchase_word_fit (u:=u) (δ:=δ) (ξ:=ξ) v.W m k v.wideJobs ell short v.stage_positive x large i)

end Frame

section Canonical
variable (dated : WideCPU.Dated (events v.mesh).length) (romStart : ℕ)
local notation "layout" => v.wideWindowProgramLayout x m ell short u δ ξ broadcast dated bits romStart
variable (fit : v.GateRoom x.h x.w bits
    (v.wideWindowProgramLayout x m ell short u δ ξ broadcast dated bits romStart) size)
local notation "realGates" => v.wideGates x.h x.w bits layout size fit
variable {X : Type} {d R M den : ℕ} {eventPin : Event→ WireTelescope.CalendarTape.Slot X} {es : List Event}
    {state : Equiv.Perm (Row x.h)→ X}
    (Z : CalendarTerms F x.h d k x.w R M den eventPin es state)
    {E H : Type} [Fintype E] [Fintype H] (cap : E→ℕ) (historyCap : H→ℕ) (dates view : ℕ)
local notation "D" => CalendarTerms.Shared (geometry).index cap historyCap (dir).groups ports (2^ell) dates view x.w
local notation "rout" => Z.nativeRouting D
local notation "ext" => OpenPins x.h x.w (rout).catalyst
local notation "sel" => Fin (rout).selectors
local notation "sites" => Fin (siteLast x.h d k+1)
local notation "V" => SitePins ext sel D (realGates).2


include fit Z cap historyCap dates view in
/-- The calibrated calendar uses its own allocated immutable pages, original role and slot
inputs, and the paid width bank on the same run. The scatter and prune phases share
one literal allocation. -/
def wideWindowLocalPrograms
    (head : (realGates).1.Head → (ext⊕sel)⊕Bool) (paidHead : (realGates).2.Head → (ext⊕sel)⊕Bool)
    (keep pad privateGate plane timeline : Net F V)
    (enter finish : sites → Net F V) (row : sites → Fin es.length → Net F V)
    (large : purchaseWordHeight v.W k v.wideJobs ell≤ x.h) :
    LocalPrograms (F:=F) (k:=k) (M:=M) x («menu»:=menu) (fun _=>slots)
      (fun i=>purchaseCandidates x.h v.W k v.wideJobs slots ((menu).height i x)
        (purchaseModules v.W u δ ξ menu x i)) :=
  v.wide_funded_local x m ell short bits broadcast (v.wideFormatROM x dated bits romStart) size
    layout fit rfl (Nat.le_refl _) Z cap historyCap dates view head paidHead keep pad privateGate plane timeline
    enter finish row large

local notation "counts" => purchaseModules v.W u δ ξ menu x
local notation "candidates" => fun i=>purchaseCandidates x.h v.W k v.wideJobs slots ((menu).height i x) (counts i)
variable {C : ℝ}

include fit Z cap historyCap dates view in
/-- The public circuit is the same object in the hardware tariff and in the native
calendar contraction, with exactly one supplied pair of compactors per real class. -/
theorem wideWindowLocalPrograms_compile
    (head : (realGates).1.Head → (ext⊕sel)⊕Bool) (paidHead : (realGates).2.Head → (ext⊕sel)⊕Bool)
    (keep pad privateGate plane timeline : Net F V)
    (enter finish : sites → Net F V) (row : sites → Fin es.length → Net F V)
    (large : purchaseWordHeight v.W k v.wideJobs ell ≤ x.h)
    (items : PurchaseList (F:=F) (C:=C) menu x (fun _=>slots) candidates counts) :
    let core := v.wideWindowLocalPrograms x m ell short bits broadcast size dated romStart fit
      Z cap historyCap dates view head paidHead keep pad privateGate plane timeline enter finish row large
    (core).compile menu x (fun _=>slots) candidates counts items =
      Z.assembled (geometry).index cap historyCap (dir).groups ports (2^ell) dates view (realGates).1 (realGates).2
        head paidHead (0 : Fin 1) keep pad privateGate plane timeline enter finish row
        (fun i=>(items i).cut ((core).read i)) (fun i=>⌊((menu).height i x:ℝ)^A⌋₊) := rfl

end Canonical


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
