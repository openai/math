import OAI.Hierarchy.TaggedWideCalendarLeaf
import OAI.Hierarchy.TaggedWideCalendarContraction

namespace OAI
/-! # Closing a retained or pruned original signed calendar branch -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
open AdaptiveProbe TaggedPrune Tagged WireTelescope WireTelescope.CalendarTape ProtocolRAM.Calendar
open ProtocolStackContraction TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts
open WideStack WideStack.Leaf WideCalendarSites
open scoped Classical BigOperators
set_option quotPrecheck false

variable {F : Type*} [Field F] {X : Type} {z d k w R M den : ℕ}
  {slots : Event→Slot X} {es : List Event} {state : Equiv.Perm (Row z)→X}
  (Z : CalendarTerms F z d k w R M den slots es state)
  (Shared : Type) [Fintype Shared] (perm : Equiv.Perm (Row z)) (i : Fin ((Z.nativeRouting Shared).count perm))
private abbrev selectedReport :=
  cursorReport perm (Z.width perm) (Z.reported perm)
    ((Prefix.histories (WireTelescope.CalendarTape.Prefix.start :
      WireTelescope.CalendarTape.Prefix slots es (state perm) es (state perm)))
      ((Fintype.equivFin (Path slots es (state perm))).symm i))

local notation "A₀" => (WireTelescope.CalendarTape.Prefix.start :
  WireTelescope.CalendarTape.Prefix slots es (state perm) es (state perm))
local notation "C" => (Prefix.cursorSlot (slot:=slots) (events:=es) (x₀:=state perm))
local notation "V₀" => Prefix.atCursor A₀
local notation "ws" => Prefix.atWidth (Z.width perm)
local notation "step" => Prefix.atStep (Z.width perm) (Z.operator perm)
local notation "rep" => cursorReport perm (Z.width perm) (Z.reported perm)
local notation "branch" => (Prefix.histories A₀) ((Fintype.equivFin (Path slots es (state perm))).symm i)
local notation "raw" => (rep branch).rows
local notation "Sites" => Fin (siteLast z d k+1)
local notation "Ext" => OpenPins z w (fun _ : Fin k=>Fintype.card (Columns z d)*R)

variable {T V : Type} [Fintype T] [Fintype V] {groups ports lanes view m n : ℕ}
    (key : T ↪ ℕ×ℕ) (positive : Fin (selectedReport Z Shared perm i).edges→Prop)
    (stage : Fin (selectedReport Z Shared perm i).edges→ℕ)
local notation "γ" => fun t:T=>(key t).2
local notation "scheduled" => fun t:T=>atScale positive stage (key t).1 raw
local notation "Free" => {u : Fin (rep branch).edges // ¬positive u}
local notation "used" => fun e:Free=>(raw e.val).width
variable (b : ∀t,Installed F groups ports lanes w m (key t).2
    (atScale positive stage (key t).1 (selectedReport Z Shared perm i).rows))
    (cap : {u : Fin (selectedReport Z Shared perm i).edges // ¬positive u}→ℕ)
local notation "B" => banks b
local notation "P" => (Fin groups×Fin ports)×Fin view
local notation "D" => Pin B cap (Fin n) P
local notation "Rout" => Z.nativeRouting Shared
local notation "Keep" => ((Rout).links ⟨perm,i⟩).Keep (2^z)
local notation "placedData" => nativePins (view:=view) key raw positive stage b cap
local notation "trace" => placedBits C ws es V₀ branch

theorem terminal_network (hw : 0<w) (room : ∀ e,used e≤cap e)
    (cover : ∀u,positive u→0<(raw u).width→∃t,key t=(stage u,widthIndex m ((raw u).width/(w:ℝ))) ∧ (raw u).group<groups)
    (ext : Ext→Bool) (place : PartyBit C ws es V₀ branch ↪ Fin n)
    (pins : (D→Bool)→V→Bool) (cut : T→CutFormat F V)
    (keep pad privateGate plane timeline : Net F V)
    (E T₁ : Sites→Net F V) (row : Sites→Fin es.length→Net F V)
    (flag : ∀d,TypedWiring.value keep (pins d)=if Keep then 1 else 0)
    (cuts : ∀ z₀ y h p t,(cut t).closed (pins (write B cap z₀ y h p))=(B t).settings.close (z₀ t))
    (masks : ∀ z₀ y h p,TypedWiring.value pad (pins (write B cap z₀ y h p))=
      if supported B (active b) z₀ then 1 else 0)
    (free : ∀ z₀ y h p,TypedWiring.value privateGate (pins (write B cap z₀ y h p))=
      if EndsPadded used cap y then privateWeight raw positive cap y else 0)
    (output : ∀ z₀ y h p,TypedWiring.value plane (pins (write B cap z₀ y h p))=
      TypedWiring.value (decoder (F:=F) (groups:=groups) (ports:=ports) (lanes:=lanes)
        (view:=view) (w:=w) key) (Sum.elim (voltage B z₀) p))
    (historyMask : ∀a h,TypedWiring.value timeline (pins (placedData a h))=
      if ∀j,h j=true→j∈Set.range place then 1 else 0)
    (first : ∀ a (q : SiteChoices C ws es V₀ branch) s,
      TypedWiring.value (E s) (pins (placedData a (trace place q))) =
        entry perm ws V₀ (Z.head perm) s (fun t=>ext (routingPort t.val)) (q s).1)
    (finish : ∀ a (q : SiteChoices C ws es V₀ branch) s,
      TypedWiring.value (T₁ s) (pins (placedData a (trace place q))) =
        (rep branch).finish s (WideCalendarSites.last C ws s es V₀ branch (q s).1 (q s).2) ((rep branch).ports a s))
    (steps : ∀ a (q : SiteChoices C ws es V₀ branch) s,
      Reads C ws step s es V₀ branch (q s).1 (q s).2 (fun j=>
        TypedWiring.value (row s j) (pins (placedData a (trace place q))))) :
    (∑ x : D→Bool,(∏t,(cut t).closed (pins x))*
      TypedWiring.value (reportedSite keep pad privateGate plane timeline (network E T₁ row)) (pins x)) =
      if Keep then (Rout).route ⟨perm,i⟩ ext else 0 := by
  rw [close_reported key raw positive stage b cap hw room cover pins cut keep pad privateGate plane timeline
    (network E T₁ row) Keep (fun j=>j∈Set.range place) flag cuts masks free output historyMask]
  by_cases kept : Keep
  · simp only [ite_eq_left kept]
    exact Z.route_site_network Shared perm i ext place (fun a h=>pins (placedData a h)) E T₁ row first finish steps
  · simp [kept]

end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms

end
end OAI
