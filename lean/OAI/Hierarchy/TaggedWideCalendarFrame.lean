import OAI.Hierarchy.TaggedWideCalendarTerminal
import OAI.Hierarchy.TaggedWidePrivateOrdinals
import OAI.Hierarchy.TaggedWidePurchasedFamily
import OAI.Hierarchy.TaggedWideDataWorkspace

namespace OAI
/-! # One shared four-block workspace for every signed native calendar branch -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
open ThreeFlat Routing
open AdaptiveProbe Tagged WireTelescope WireTelescope.CalendarTape ProtocolRAM.Calendar TaggedPrune
open TaggedShorterBudget ProtocolStackContraction TaggedShorterFields ProtocolRAMReportedPorts
open WideStack WideCalendarSites WideControlJoin
open scoped Classical BigOperators
set_option quotPrecheck false

/-- Every public menu slot, private pair, timeline position and decoded output has
the same address for every selector and matching. -/
abbrev Shared {H : Type} [Fintype H] {T E : Type}
    (key : T ↪ ℕ×ℕ) (cap : E→ℕ) (historyCap : H→ℕ)
    (groups ports lanes dates view w : ℕ) :=
  DataWorkspace T (Fin groups) E H ports lanes dates view (fun t=>⌈dyadic (key t).2*w⌉₊) cap historyCap

/-- Numbering the private rows on the complete native report board preserves both
ends, each bit position, every public port, and all chronological assignments. -/
def privateWorkspace {E₁ E₂ H T : Type} [Fintype H] (key : T ↪ ℕ×ℕ)
    (order : E₁ ≃ E₂) (cap : E₂→ℕ) (historyCap : H→ℕ) (groups ports lanes dates view w : ℕ) :
    Shared key (cap ∘ order) historyCap groups ports lanes dates view w ≃
      Shared key cap historyCap groups ports lanes dates view w :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.prodCongr (Equiv.refl _)
    (Equiv.sigmaCongrLeft (β:=fun e=>Fin (cap e)) order)) (Equiv.refl _))

variable {F : Type*} [Field F] {X : Type} {z d k w R M den : ℕ}
    {slots : Event→Slot X} {es : List Event} {state : Equiv.Perm (Row z)→X}
    (Z : CalendarTerms F z d k w R M den slots es state)
    {H T Q : Type} [Fintype H] [Fintype T] [Fintype Q] (key : T ↪ ℕ×ℕ)
    (cap : Q→ℕ) (historyCap : H→ℕ) (groups ports lanes dates view : ℕ)
local notation "D" => Shared key cap historyCap groups ports lanes dates view w
local notation "rout" => Z.nativeRouting D
local notation "E₀" => OpenPins z w (rout).catalyst
local notation "sels" => Fin (rout).selectors
local notation "sites" => Fin (siteLast z d k+1)
private abbrev gateInput := (E₀ ⊕ sels) ⊕ Bool
private abbrev circuitPins (paid : Gate) := SitePins E₀ sels D paid

variable (A B : Gate)
    (prefixPins : A.Head → gateInput Z key cap historyCap groups ports lanes dates view)
    (paidPins : B.Head → gateInput Z key cap historyCap groups ports lanes dates view)
    (flag : Fin A.u)
local notation "V" => SitePins E₀ sels D B
variable (keep pad privateGate plane timeline :
      Net F (circuitPins Z key cap historyCap groups ports lanes dates view B))
    (entry finish : Fin (siteLast z d k+1) →
      Net F (circuitPins Z key cap historyCap groups ports lanes dates view B))
    (row : Fin (siteLast z d k+1) → Fin es.length →
      Net F (circuitPins Z key cap historyCap groups ports lanes dates view B))

/-- The actual external table installed in the common frame includes both physical
endpoints and every signed local operation at its public date. -/
def frame : Frame F k z w M where
  routing := rout
  data := D
  first := A
  paid := B
  prefixPins := prefixPins
  paidPins := paidPins
  flag := flag
  site := reportedSite keep pad privateGate plane timeline (network entry finish row)

local notation "a" => Z.frame key cap historyCap groups ports lanes dates view A B prefixPins paidPins
    flag keep pad privateGate plane timeline entry finish row

/-- All charged cells and internal wires of the site block, including both
endpoint tables at each physical site and all the per-date local operations. -/
theorem frame_site_charge {l : ℕ} (cut : Fin l→CutFormat F V) :
    (nativeCharges rout A B cut (a).site).site =
      keep.cells+keep.internal+((pad.cells+pad.internal)+((privateGate.cells+privateGate.internal)+
      ((plane.cells+plane.internal)+((timeline.cells+timeline.internal)+
      ∑ s, ((finish s).cells+(finish s).internal+(((entry s).cells+(entry s).internal)+
        ∑ j,((row s j).cells+(row s j).internal))))))) := by
  change (reportedSite keep pad privateGate plane timeline (network entry finish row)).cells+
    (reportedSite keep pad privateGate plane timeline (network entry finish row)).internal=_
  rw [reported_cost,network_size]

/-- Reindex the literal physical common-data assignment for a selected branch. -/
theorem frame_sum {D' : Type} [Fintype D'] (ord : D' ≃ D) (ext : E₀→Bool)
    (sel : sels→Bool) (seen : B.Seen→Bool)
    {l : ℕ} (cut : Fin l→CutFormat F V) :
    (∑d : (a).data→Bool,(∏i,(cut i).closed (Sum.elim ext (Sum.elim sel (Sum.elim d seen))))*
        localSite (a).paid (a).site ext sel d seen) =
      ∑d : D'→Bool,(∏i,(cut i).closed (Sum.elim ext (Sum.elim sel (Sum.elim (d ∘ ord.symm) seen))))*
        TypedWiring.value (reportedSite keep pad privateGate plane timeline (network entry finish row))
          (Sum.elim ext (Sum.elim sel (Sum.elim (d ∘ ord.symm) seen))) := by
  let e := Equiv.arrowCongr ord (Equiv.refl Bool)
  exact (e.sum_comp (fun d=>(∏i,(cut i).closed (Sum.elim ext (Sum.elim sel (Sum.elim d seen))))*
    localSite (a).paid (a).site ext sel d seen)).symm

end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms

end
end OAI
