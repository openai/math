import OAI.Hierarchy.TaggedWideRankedCuts

namespace OAI
/-! # The four native signed operations complete the common funded receipt -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
open AdaptiveProbe TaggedPrune Tagged WireTelescope WireTelescope.CalendarTape ProtocolRAM.Calendar
open ProtocolStackContraction TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts
open WideStack WideStack.Leaf WideCalendarSites WideControlJoin
open scoped Classical BigOperators
set_option quotPrecheck false

variable {F : Type} [Field F] {X : Type} {z d k w R M den : ℕ}
    {slots : Event→Slot X} {es : List Event} {state : Equiv.Perm (Row z)→X}
    (Z : CalendarTerms F z d k w R M den slots es state) {L groups ports lanes view m n : ℕ}
    {S : Type} [Fintype S] (key : Fin L ↪ ℕ×ℕ) (B₁ : Gate)
local notation "Rout" => Z.nativeRouting S
private abbrev rankedPins :=
  SitePins (OpenPins z w (Z.nativeRouting S).catalyst) (Fin (Z.nativeRouting S).selectors) S B₁
variable (cut : Fin L→CutFormat F (rankedPins Z B₁ (S:=S)))
    (keep pad privateGate plane timeline : Net F (rankedPins Z B₁ (S:=S)))
    (E T₁ : Fin (siteLast z d k+1)→Net F (rankedPins Z B₁ (S:=S)))
    (row : Fin (siteLast z d k+1)→Fin es.length→Net F (rankedPins Z B₁ (S:=S)))
    (perm : Equiv.Perm (Row z)) (i : Fin ((Z.nativeRouting S).count perm))
    (ext : OpenPins z w (Z.nativeRouting S).catalyst→Bool)
    (sel : Fin (Z.nativeRouting S).selectors→Bool) (seen : B₁.Seen→Bool)
local notation "A₀" => (WireTelescope.CalendarTape.Prefix.start :
  WireTelescope.CalendarTape.Prefix slots es (state perm) es (state perm))
local notation "C" => (Prefix.cursorSlot (slot:=slots) (events:=es) (x₀:=state perm))
local notation "V₀" => Prefix.atCursor A₀
local notation "ws" => Prefix.atWidth (Z.width perm)
local notation "step" => Prefix.atStep (Z.width perm) (Z.operator perm)
local notation "rep" => cursorReport perm (Z.width perm) (Z.reported perm)
local notation "branch" => (Prefix.histories A₀) ((Fintype.equivFin (Path slots es (state perm))).symm i)
local notation "raw" => (rep branch).rows
local notation "Keep" => ((Rout).links ⟨perm,i⟩).Keep (2^z)
local notation "trace" => placedBits C ws es V₀ branch
local notation "γ" => fun t:Fin L=>(key t).2
local notation "P" => (Fin groups×Fin ports)×Fin view


private abbrev rankedBoard : RowBoard := ⟨(rep branch).edges,raw⟩
private abbrev rankedParty := PartyBit C ws es V₀ branch

variable (r : RankedRows (F:=F) key S groups ports lanes w m n view (rankedBoard Z (S:=S) perm i))
    (place : rankedParty Z (S:=S) perm i ↪ Fin n)

/-- The history support, first state, last state and successive signed site
matrices are all measured on the same original row-word and party embedding. -/
structure RankedRows.Endpoints : Prop where
  historyMask : ∀a h,TypedWiring.value timeline (readPins (B:=B₁) r.numbering ext sel seen
    (nativePins (view:=view) key raw r.positive r.stage r.installed r.cap a h))=
      if ∀j,h j=true→j∈Set.range place then 1 else 0
  first : ∀a (q : SiteChoices C ws es V₀ branch) s,TypedWiring.value (E s) (readPins (B:=B₁) r.numbering ext sel seen
    (nativePins (view:=view) key raw r.positive r.stage r.installed r.cap a (trace place q))) =
    entry perm ws V₀ (Z.head perm) s (fun t=>ext (routingPort t.val)) (q s).1
  finish : ∀a (q : SiteChoices C ws es V₀ branch) s,TypedWiring.value (T₁ s) (readPins (B:=B₁) r.numbering ext sel seen
    (nativePins (view:=view) key raw r.positive r.stage r.installed r.cap a (trace place q))) =
    (rep branch).finish s (WideCalendarSites.last C ws s es V₀ branch (q s).1 (q s).2) ((rep branch).ports a s)
  steps : ∀a (q : SiteChoices C ws es V₀ branch) s,Reads C ws step s es V₀ branch (q s).1 (q s).2
    (fun j=>TypedWiring.value (row s j) (readPins (B:=B₁) r.numbering ext sel seen
      (nativePins (view:=view) key raw r.positive r.stage r.installed r.cap a (trace place q))))

def RankedRows.receipt
    (ranks : RankedRows.Bounds r)
    (pairs : RankedRows.CutsAndMask B₁ r cut pad ext sel seen)
    (fields : RankedRows.PrivatePlane B₁ r privateGate plane ext sel seen)
    (retention : ∀d,TypedWiring.value keep (readPins (B:=B₁) r.numbering ext sel seen d)=if Keep then 1 else 0)
    (sites : RankedRows.Endpoints Z key B₁ timeline E T₁ row perm i ext sel seen r place) :
    Z.Receipt key B₁ cut keep pad privateGate plane timeline E T₁ row perm i ext sel seen
      groups ports lanes view m n where
  positive := r.positive
  stage := r.stage
  installed := r.installed
  cap := r.cap
  numbering := r.numbering
  place := place
  room := ranks.room
  cover := ranks.cover
  flag := retention
  cuts := pairs.cuts
  masks := pairs.masks
  free := fields.free
  output := fields.output
  historyMask := sites.historyMask
  first := sites.first
  finish := sites.finish
  steps := sites.steps

end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
end

end OAI
