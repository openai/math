import OAI.Hierarchy.TaggedWideCalendarFrame
import OAI.Hierarchy.TaggedWideRetentionBit

namespace OAI
/-! # Local observations for a fixed frame on an original native branch -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
open AdaptiveProbe TaggedPrune Tagged WireTelescope WireTelescope.CalendarTape ProtocolRAM.Calendar
open ProtocolStackContraction TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts
open WideStack WideStack.Leaf WideCalendarSites WideControlJoin
open scoped Classical BigOperators
set_option quotPrecheck false

def readPins {Ex Se D U : Type} {B : Gate} (ord : U ≃ D) (ext : Ex→Bool) (sel : Se→Bool)
    (seen : B.Seen→Bool) (assignment : U→Bool) : SitePins Ex Se D B→Bool :=
  Sum.elim ext (Sum.elim sel (Sum.elim (assignment ∘ ord.symm) seen))

variable {F : Type*} [Field F] {X : Type} {z d k w R M den : ℕ}
    {slots : Event→Slot X} {es : List Event} {state : Equiv.Perm (Row z)→X}
    (Z : CalendarTerms F z d k w R M den slots es state) {L groups ports lanes view m n : ℕ}
    {S : Type} [Fintype S] (key : Fin L ↪ ℕ×ℕ) (B₁ : Gate)
local notation "Rout" => Z.nativeRouting S
private abbrev receiptPins :=
  SitePins (OpenPins z w (Z.nativeRouting S).catalyst) (Fin (Z.nativeRouting S).selectors) S B₁
variable (cut : Fin L→CutFormat F (receiptPins Z B₁ (S:=S)))
    (keep pad privateGate plane timeline : Net F (receiptPins Z B₁ (S:=S)))
    (E T₁ : Fin (siteLast z d k+1)→Net F (receiptPins Z B₁ (S:=S)))
    (row : Fin (siteLast z d k+1)→Fin es.length→Net F (receiptPins Z B₁ (S:=S)))
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

/-- The statements concerning the fixed frame are individual cell evaluations
at native observations. In particular the receipt never stores a value for the
complete selected tensor. -/
structure Receipt (groups ports lanes view m n : ℕ) where
  positive : Fin (rep branch).edges→Prop
  stage : Fin (rep branch).edges→ℕ
  installed : ∀t,Installed F groups ports lanes w m (γ t) (atScale positive stage (key t).1 raw)
  cap : {u : Fin (rep branch).edges // ¬positive u}→ℕ
  numbering : Pin (banks installed) cap (Fin n) ((Fin groups×Fin ports)×Fin view) ≃ S
  place : PartyBit C ws es V₀ branch ↪ Fin n
  room : ∀e,(raw e.val).width≤cap e
  cover : ∀u,positive u→0<(raw u).width→∃t,key t=(stage u,widthIndex m ((raw u).width/(w:ℝ))) ∧
    (raw u).group<groups
  flag : ∀d,TypedWiring.value keep (readPins (B:=B₁) numbering ext sel seen d)=if Keep then 1 else 0
  cuts : ∀a y h p t,(cut t).closed (readPins (B:=B₁) numbering ext sel seen (write (banks installed) cap a y h p))=
    ((banks installed) t).settings.close (a t)
  masks : ∀a y h p,TypedWiring.value pad (readPins (B:=B₁) numbering ext sel seen (write (banks installed) cap a y h p))=
    if supported (banks installed) (active installed) a then 1 else 0
  free : ∀a y h p,TypedWiring.value privateGate (readPins (B:=B₁) numbering ext sel seen (write (banks installed) cap a y h p))=
    if EndsPadded (fun e=>(raw e.val).width) cap y then privateWeight raw positive cap y else 0
  output : ∀a y h p,TypedWiring.value plane (readPins (B:=B₁) numbering ext sel seen (write (banks installed) cap a y h p))=
    TypedWiring.value (decoder (F:=F) (groups:=groups) (ports:=ports) (lanes:=lanes)
      (view:=view) (w:=w) key) (Sum.elim (voltage (banks installed) a) p)
  historyMask : ∀a h,TypedWiring.value timeline (readPins (B:=B₁) numbering ext sel seen
    (nativePins (view:=view) key raw positive stage installed cap a h))=
      if ∀j,h j=true→j∈Set.range place then 1 else 0
  first : ∀a (q : SiteChoices C ws es V₀ branch) s,TypedWiring.value (E s) (readPins (B:=B₁) numbering ext sel seen
    (nativePins (view:=view) key raw positive stage installed cap a (trace place q))) =
    entry perm ws V₀ (Z.head perm) s (fun t=>ext (routingPort t.val)) (q s).1
  finish : ∀a (q : SiteChoices C ws es V₀ branch) s,TypedWiring.value (T₁ s) (readPins (B:=B₁) numbering ext sel seen
    (nativePins (view:=view) key raw positive stage installed cap a (trace place q))) =
    (rep branch).finish s (WideCalendarSites.last C ws s es V₀ branch (q s).1 (q s).2) ((rep branch).ports a s)
  steps : ∀a (q : SiteChoices C ws es V₀ branch) s,Reads C ws step s es V₀ branch (q s).1 (q s).2
    (fun j=>TypedWiring.value (row s j) (readPins (B:=B₁) numbering ext sel seen
      (nativePins (view:=view) key raw positive stage installed cap a (trace place q))))

variable (c : Z.Receipt key B₁ cut keep pad privateGate plane timeline E T₁ row perm i ext sel seen
    groups ports lanes view m n)

include c in
/-- The entire terminal clause of a physical frame follows from native wire
observations even when the original catalogue ordinals differ from the frame
ordinals. -/
theorem Receipt.terminal (hw : 0<w) :
    (∑ a : S→Bool,(∏t,(cut t).closed (Sum.elim ext (Sum.elim sel (Sum.elim a seen))))*
      localSite B₁ (reportedSite keep pad privateGate plane timeline (network E T₁ row)) ext sel a seen) =
      if Keep then (Rout).route ⟨perm,i⟩ ext else 0 := by
  let f := fun a : S→Bool=>(∏t,(cut t).closed (Sum.elim ext (Sum.elim sel (Sum.elim a seen))))*
      localSite B₁ (reportedSite keep pad privateGate plane timeline (network E T₁ row)) ext sel a seen
  let e := Equiv.arrowCongr c.numbering (Equiv.refl Bool)
  calc
    _ = ∑ a,f (e a) := (e.sum_comp f).symm
    _ = _ := Z.terminal_network S perm i key c.positive c.stage c.installed c.cap hw c.room c.cover ext c.place
      (readPins (B:=B₁) c.numbering ext sel seen) cut keep pad privateGate plane timeline E T₁ row
      c.flag c.cuts c.masks c.free c.output c.historyMask c.first c.finish c.steps

end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms

end
end OAI
