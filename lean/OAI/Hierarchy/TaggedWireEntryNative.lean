import OAI.Hierarchy.TaggedWireEntryStatic

namespace OAI
/-! # A fixed physical equality network computes the true exposed matrix -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.EntryOrder
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
open WireTelescope WireTelescope.CalendarTape TaggedPrune Tagged Catalyst AdaptiveProbe HistoryRoles ReportSockets
open scoped Classical
variable {h W k w R epochs n : ℕ}
variable (S : PurchaseSampler) (p : Equiv.Perm (Row h)) (depth : ℕ) (marked : Marks h W k epochs)
local notation "Src" => HistoryRoles.Source S p.symm depth marked
local notation "τ" => exposedSite h (2^W) k w R
local notation "U" => exposedWidth p (2^W) k w R
local notation "edges" rows => fun j=> sorted S p.symm depth marked (rows j)
local notation "amount" rows => fun j=> sourceWidth S p depth marked w R (rows j)

variable (unique : Exclusive marked) (rows : Fin n≃HistoryRoles.Source S p.symm depth marked)
variable (cap : Public S h W k epochs→ℕ)
abbrev InitialRoom (width reserve : ℕ) : Prop :=
  ∀(j : Fin n) (b : Bool),sourceWidth S p depth marked width reserve (rows j)≤
    cap (named S p.symm depth marked unique rows (j,b))

def initialState (room : InitialRoom S p depth marked unique rows cap w R)
    (values : Public S h W k epochs→ℕ→Bool) (s : Fin (siteLast h (2^W) k+1)) : State U s :=
  (siteBits U s).symm fun b=>
    let aggregate := source_aggregate (w:=w) (R:=R) S p depth marked rows
    let input : Σ t,SiteBit (installedWidths (edges rows) (amount rows)) t :=
      ⟨s,NamedAperture.transportAt aggregate.symm b⟩
    let address : Σ socket,Fin (cap socket) := NamedAperture.place (edges rows) (amount rows) (named S p.symm depth marked unique rows) cap room input
    values address.1 address.2.val

variable (room : InitialRoom S p depth marked unique rows cap w R)
variable (values : Public S h W k epochs→ℕ→Bool)

def fixedPins {s : Fin (siteLast h (2^W) k+1)} (x : {i // τ i=s}→Bool) :
    Equality.Pins (Fintype.card {i // τ i=s})→Bool :=
  fun a=> let pin:=(Fintype.equivFin {i // τ i=s}).symm a.1
         if a.2=0 then true else if a.2=1 then x pin else values (publicPort S pin.1) (publicDigit pin.1)

private theorem inverse_at {l : ℕ} {A B : Widths l} (eq : A=B) {s : Fin l} (b : SiteBit A s) :
    NamedAperture.transportAt eq.symm (NamedAperture.transportAt eq b)=b := by subst B;rfl

theorem fixed_pins {s : Fin (siteLast h (2^W) k+1)} (x : {i // τ i=s}→Bool) :
    let z:=initialState S p depth marked unique rows cap room values s
    let eq:=exposed_width (d:=2^W) (k:=k) (w:=w) (R:=R) p
    fixedPins S values x=MatchingEntry.exteriorView p τ (exposedDistinct p) (exposedOrder h (2^W) k w R) x
      (cast (congrArg (fun A=> State A s) eq.symm) z) := by
  intro z eq
  funext a
  let orig:=(Fintype.equivFin {i // τ i=s}).symm a.1
  have idx:(Fintype.equivFin _ orig)=a.1:=(Fintype.equivFin _).apply_symm_apply _
  obtain ⟨ordinal,tag⟩:=a
  fin_cases tag
  · rfl
  · rfl
  · change values (publicPort S orig.1) (publicDigit orig.1)=_
    let view:=MatchingEntry.exteriorView p τ (exposedDistinct p) (exposedOrder h (2^W) k w R) x
      (cast (congrArg (fun A=> State A s) eq.symm) z)
    refine Eq.trans (b:=view ((Fintype.equivFin _ orig),2)) ?_ (congrArg (fun i=> view (i,2)) idx)
    rw [show view ((Fintype.equivFin _ orig),2)=_ from exterior_read S p depth marked rows x z orig]
    simp only [z,initialState,Equiv.apply_symm_apply]
    obtain ⟨location,bit⟩:=static_address S p depth marked unique rows cap room orig
    let aggregate:=source_aggregate (w:=w) (R:=R) S p depth marked rows
    let pin:=sourcePortFor S p depth marked rows ((MatchingEntry.atExterior p τ s).symm orig)
    let coordinate:=NamedAperture.atPort (edges rows) (amount rows) pin
    let read (u : SiteBit (installedWidths (edges rows) (amount rows)) s) :=
      let address:=NamedAperture.place (edges rows) (amount rows) (named S p.symm depth marked unique rows) cap room ⟨s,u⟩
      values address.1 address.2.val
    exact (congrArg₂ values location.symm bit.symm).trans
      (congrArg read (inverse_at aggregate coordinate).symm)

/-- Each input of the fixed equality circuit is a constant, a literal external bit,
or a fixed bit of a public physical socket. -/
theorem fixed_read (F : Type*) [Field F] (s : Fin (siteLast h (2^W) k+1)) (x : {i // τ i=s}→Bool) :
    TypedWiring.value (MatchingEntry.fixedNetwork τ F s) (fixedPins S values x)=
      exposedMatrix p (2^W) k w R s x (initialState S p depth marked unique rows cap room values s) := by
  rw [fixed_pins S p depth marked unique rows cap room values x]
  exact fixed_exposedMatrix (F:=F) p s x _

end Hierarchy.ProbeStage.CoreBoard.EntryOrder
end

end OAI
