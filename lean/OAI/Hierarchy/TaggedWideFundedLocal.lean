import OAI.Hierarchy.TaggedWideFundedCutPins
import OAI.Hierarchy.TaggedWidePurchaseTransport

namespace OAI
/-! # The fixed positive-cut pin map in the chronological calendar frame -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open ThreeFlat Routing
open AdaptiveProbe Tagged WireTelescope WireTelescope.CalendarTape ProtocolRAM.Calendar TaggedPrune
open TaggedShorterBudget TaggedShorterSupergroups ProtocolStackContraction
open WideStack WideControlJoin WideCalendarSites ProbeStage.CoreBoard.PhysicalTerm
open scoped Classical BigOperators
set_option quotPrecheck false

variable {F : Type} [Field F] {κ A δ ξ : ℝ} {u : ℝ→ℝ} {k M den d R : ℕ}
variable (W m attempts ell short : ℕ) (hW : 0<W) (x : WideParent κ A)
local notation "geom" => typeMenu κ A W m k attempts ell hW (fun _=>short+ell)
local notation "menu" => (geom).menu u δ ξ
local notation "roles" => copies k attempts
local notation "dir" => stageDir x.h W roles (2*roles) (show 2*roles≤2^(2*roles) from Nat.lt_two_pow_self.le)
local notation "ports" => 2^(superAddress W (2*roles) x.h)
local notation "lanes" => 2^ell
local notation "slots" => purchaseSlots x.h W k attempts ell
local notation "count" => purchaseModules W u δ ξ menu x
local notation "height" => fun i : Fin (m+1)=>(menu).height i x
local notation "half" => fun i : Fin (m+1)=>2^(height i-1)
local notation "C" => fun i : Fin (m+1)=>TaggedShorterGroups.capacity (Fin (dir).groups) slots (half i) (count i)
local notation "S" => fun i : Fin (m+1)=>purchaseCandidates x.h W k attempts slots (height i) (count i)

variable {X : Type} {p : Event→Slot X} {es : List Event} {state : Equiv.Perm (Tagged.Row x.h)→X}
    (Z : CalendarTerms F x.h d k x.w R M den p es state)
    {T H : Type} [Fintype T] [Fintype H] (cap : T→ℕ) (historyCap : H→ℕ) (dates view : ℕ)
local notation "D" => CalendarTerms.Shared (geom).index cap historyCap (dir).groups ports lanes dates view x.w
local notation "rout" => Z.nativeRouting D
local notation "ext" => OpenPins x.h x.w (rout).catalyst
local notation "sel" => Fin (rout).selectors
local notation "sites" => Fin (CoreBoard.siteLast x.h d k+1)
variable (first paid : Gate)
local notation "V" => SitePins ext sel D paid

/-- Only the original signed programs, their static layout and the chronological
site factors enter this construction. No selected copy or private assignment is used. -/
def fundedLocalPrograms (head : first.Head→(ext⊕sel)⊕Bool) (paidHead : paid.Head→(ext⊕sel)⊕Bool)
    (flag : Fin first.u) (keep pad privateGate plane timeline : Net F V)
    (enter finish : sites→Net F V) (row : sites→Fin es.length→Net F V)
    (base : Fin (m+1)→ℕ)
    (room : ∀i,base i+(C i+2*(C i*2*slots))≤paid.u)
    (bits : ∀i,height i≤paid.W) :
    LocalPrograms (F:=F) (k:=k) (M:=M) x («menu»:=menu) (fun _=>slots) S where
  frame := Z.frame (geom).index cap historyCap (dir).groups ports lanes dates view first paid head paidHead
    flag keep pad privateGate plane timeline enter finish row
  read i := by
    change TaggedShorterCompaction.Input (S i) slots (height i+(menu).payload i x) → V
    have eqn : S i=C i := (purchase_capacity (dir).groups slots (half i) (count i)).symm
    refine Purchased.readAt («D»:=slots) (width:=height i+(menu).payload i x) («V»:=V) eqn ?_
    exact frozenReadPin (Fin (dir).groups) slots (half i) (count i) (height i) ((menu).payload i x)
      (base i) (room i) (bits i) (calendarSlot (G:=Fin (dir).groups) («ports»:=ports) («lanes»:=lanes)
        (dates:=dates) (view:=view) (width:=fun t=>(menu).payload t x)
        (privateCap:=cap) (historyCap:=historyCap) i)

end Hierarchy.ProbeStage.ReportSockets

end
end OAI
