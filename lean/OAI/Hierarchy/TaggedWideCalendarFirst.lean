import OAI.Hierarchy.TaggedWideCalendarReceipt
import OAI.Hierarchy.TaggedWireEntryStateRead
import OAI.Hierarchy.TaggedWireTimelineLast

namespace OAI
/-! # The initial matching aperture in the fixed physical calendar -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open LinearAlgebra.SpectralBooks ChordGraph ProtocolRAM.Calendar
open scoped Classical
variable {n : ℕ} {X Q : Type} [Fintype Q] (slot : Event→Slot X) (wire : X→Widths n)
    (cells : ∀y,(Σs,SiteBit (wire y) s) ↪ Q)

theorem first_body (es : List Event) (x : X) (j : Path slot es x)
    (z : SiteChoices slot wire es x j) (s : Fin n) (b : SiteBit (wire x) s) :
    placedBits slot wire es x j (timelineFin slot wire cells es x j) z (bodyIndex es 0 (cells x ⟨s,b⟩))=
      siteBits (wire x) s (z s).1 b := by
  let q : PartyBit slot wire es x j:=⟨s,.inl b⟩
  have addr : timelineFin slot wire cells es x j q=bodyIndex es 0 (cells x ⟨s,b⟩) :=
    congrArg (fun a : Fin (es.length+1)×Q=>bodyIndex es a.1 a.2) (timeline_head slot wire cells es x j s b)
  rw [←addr]
  exact placed_at slot wire es x j (timelineFin slot wire cells es x j) z q

end Hierarchy.WireTelescope.CalendarTape

namespace Hierarchy.ProbeStage.CoreBoard.EntryOrder
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
open AdaptiveProbe TaggedPrune Tagged Catalyst HistoryRoles ReportSockets
open WireTelescope WireTelescope.CalendarTape ProtocolRAM.Calendar
open Tagged.WideControlJoin ProtocolStackContraction TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts
open Tagged.WideStack Tagged.WideStack.Leaf Tagged.WideCalendarSites
open scoped Classical BigOperators
set_option quotPrecheck false
set_option maxHeartbeats 170000

private theorem packed_site {n : ℕ} {A B C : Widths n} {H : Type}
    (head : A=B) (stock : C=A) (aperture : (Σs,SiteBit C s) ↪ H)
    (read : (Σs,SiteBit B s) ↪ H)
    (placement : read=(NamedAperture.transport head.symm).toEmbedding.trans
      ((NamedAperture.transport stock.symm).toEmbedding.trans aperture))
    {s : Fin n} (u : SiteBit A s) :
    read ⟨s,NamedAperture.transportAt head u⟩ =
      aperture ⟨s,NamedAperture.transportAt stock.symm u⟩ := by
  subst B
  subst C
  subst read
  rfl

private theorem rewidth_read {n : ℕ} {A B : Widths n} (eqn : A=B) {s : Fin n} (u : SiteBit A s) (v : State B s) :
    siteBits B s v (NamedAperture.transportAt eqn u)=siteBits A s (cast (congrArg (fun V=>State V s) eqn.symm) v) u := by subst B;rfl

private theorem rewidth_value {n : ℕ} {F : Type*} {Leg : Fin n→Type} {A B : Widths n} (eqn : A=B)
    (M : SiteMatrix Leg (State A) F) (s : Fin n) (x : Leg s) (v : State B s) :
    M s x (cast (congrArg (fun V=>State V s) eqn.symm) v)=MatchingEntry.rewidth eqn M s x v := by subst B;rfl

variable {X : Type} {h W k w R attempts n : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Row h))
    (depth : ℕ) (marked : Marks h W k attempts) (unique : Exclusive marked)
    (rows : Fin n≃HistoryRoles.Source S π.symm depth marked)
local notation "τ" => exposedSite h (2^W) k w R
local notation "U" => exposedWidth π (2^W) k w R
local notation "N" => siteLast h (2^W) k+1
local notation "Roles" => Public S h W k attempts
variable (cap : Public S h W k attempts→ℕ)
    (room : InitialRoom S π depth marked unique rows cap w R)
local notation "Times" => (u:Roles) × Fin (cap u)
variable (slot : Event→Slot X) (wire : X→Widths (siteLast h (2^W) k+1))
    (cells : ∀y,(Σs,SiteBit (wire y) s) ↪ ((u : Public S h W k attempts) × Fin (cap u)))
    (es : List Event) (x : X) (j : Path slot es x) (head : exposedWidth π (2^W) k w R=wire x)
local notation "aggregate" => source_aggregate (w:=w) (R:=R) S π depth marked rows
local notation "place" => NamedAperture.place (fun i=>sorted S π.symm depth marked (rows i))
    (fun i=>sourceWidth S π depth marked w R (rows i)) (named S π.symm depth marked unique rows) cap room
variable (packing : cells x=(NamedAperture.transport head.symm).toEmbedding.trans
    ((NamedAperture.transport (source_aggregate (w:=w) (R:=R) S π depth marked rows).symm).toEmbedding.trans
      (NamedAperture.place (fun i=>sorted S π.symm depth marked (rows i))
        (fun i=>sourceWidth S π depth marked w R (rows i)) (named S π.symm depth marked unique rows) cap room)))
local notation "Time" => Fin ((es.length+1)*Fintype.card Times)

def firstSocket (hist : Time→Bool) (u : Roles) (i : ℕ) : Bool :=
  if hi : i<cap u then hist (bodyIndex es 0 (⟨u,i,hi⟩:Times)) else false

include packing in
/-- The actual first site state follows from the genuine initial named socket
embedding and the shared history tape. -/
theorem first_state (z : SiteChoices slot wire es x j) (s : Fin N) :
    initialState S π depth marked unique rows cap room
      (firstSocket S cap es (placedBits slot wire es x j (timelineFin slot wire cells es x j) z)) s=
      cast (congrArg (fun V=>State V s) head.symm) (z s).1 := by
  apply (siteBits U s).injective
  funext u
  let old := NamedAperture.transportAt (aggregate).symm u
  let loc := place ⟨s,old⟩
  have here : cells x ⟨s,NamedAperture.transportAt head u⟩=loc :=
    packed_site head aggregate place (cells x) packing u
  simp only [initialState,Equiv.apply_symm_apply]
  change firstSocket S cap es _ loc.1 loc.2.val=_
  rw [firstSocket,dite_eq_left loc.2.isLt]
  change placedBits slot wire es x j (timelineFin slot wire cells es x j) z (bodyIndex es 0 loc)=_
  let tape := placedBits slot wire es x j (timelineFin slot wire cells es x j) z
  exact (congrArg (fun t : Times => tape (bodyIndex es 0 t)) here.symm).trans
    ((first_body slot wire cells es x j z s (NamedAperture.transportAt head u)).trans
      (rewidth_read head u (z s).1))

variable {Ex Se D : Type} [Fintype Ex] [Fintype Se] [Fintype D] (B : Gate)
    (bound : Fin ((es.length+1)*Fintype.card ((u : Public S h W k attempts) × Fin (cap u))) ↪ D) (extPort : RoutingPin h w (fun _ : Fin k=>Fintype.card (Columns h (2^W))*R)→Ex)

def firstPin (s : Fin N) (a : Equality.Pins (Fintype.card {i // τ i=s})) : SitePins Ex Se D B⊕Bool :=
  let q:=(Fintype.equivFin {i // τ i=s}).symm a.1
  let u : Public S h W k attempts:=publicPort S q.val
  let i:=publicDigit q.val
  if a.2=0 then .inr true else if a.2=1 then .inl (.inl (extPort q.val))
  else if hi : i<cap u then .inl (.inr (.inr (.inl (bound (bodyIndex es 0 (⟨u,i,hi⟩ : Times)))))) else .inr false

def firstNetwork (F : Type*) [Field F] (s : Fin N) : BitNetwork F (Fintype.card (SitePins Ex Se D B)) :=
  WideHost.localFamily (I:=Unit) (V:=SitePins Ex Se D B)
    (A:=fun _=>Equality.Pins (Fintype.card {i // τ i=s}))
    (fun _=>MatchingEntry.fixedNetwork τ F s) (fun _=>firstPin S cap es B bound extPort s)

theorem first_cost (F : Type*) [Field F] (s : Fin N) :
    let E:=firstNetwork (Se:=Se) S cap es B bound extPort F s
    E.cells+E.internal=(MatchingEntry.fixedNetwork τ F s).cells+(MatchingEntry.fixedNetwork τ F s).internal := by
  intro E
  rw [show E.cells+E.internal=_ from WideHost.localFamily_size ..]
  simp

include packing in
theorem first_value {F : Type*} [Field F]
    (z : SiteChoices slot wire es x j) (s : Fin N) (external : Ex→Bool) (sel : Se→Bool) (seen : B.Seen→Bool)
    (data : D→Bool) (timeRead : ∀t,data (bound t)=placedBits slot wire es x j (timelineFin slot wire cells es x j) z t) :
    TypedWiring.value (firstNetwork S cap es B bound extPort F s)
      (PhysicalTerm.CalendarTerms.readPins (B:=B) (Equiv.refl D) external sel seen data)=
      PhysicalTerm.entry π wire x head s (fun i=>external (extPort i.val)) (z s).1 := by
  rw [firstNetwork,WideHost.localFamily_eval,Fintype.prod_unique]
  let hist:=placedBits slot wire es x j (timelineFin slot wire cells es x j) z
  have pins : (Sum.elim (PhysicalTerm.CalendarTerms.readPins (B:=B) (Equiv.refl D) external sel seen data) id ∘
      firstPin S cap es B bound extPort s)=
      fixedPins S (firstSocket S cap es hist) (fun i=>external (extPort i.val)) := by
    funext i
    simp only [Function.comp_apply]
    unfold firstPin fixedPins firstSocket
    dsimp only
    split_ifs <;> first | rfl | exact timeRead _
  rw [pins,fixed_read S π depth marked unique rows cap room]
  rw [first_state S π depth marked unique rows cap room slot wire cells es x j head packing]
  unfold PhysicalTerm.entry
  exact rewidth_value (F:=F) head (exposedMatrix (F:=F) π (2^W) k w R) s
    (fun i=>external (extPort i.val)) (z s).1

/-- The time component of the numbered shared data bank. -/
def timePin {A C Q P D : Type} (ord : (A ⊕ (C ⊕ (Q ⊕ P))) ≃ D) : Q ↪ D :=
  ⟨fun t=>ord (.inr (.inr (.inl t))),fun _ _ h=>Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (ord.injective h)))⟩

section Contracted
variable {F : Type*} [Field F] {L nRows groups ports lanes m view : ℕ}
    (key : Fin L ↪ ℕ×ℕ) (raw : Fin nRows→ProtocolRAMEmit.Row) (positive : Fin nRows→Prop)
    (stage : Fin nRows→ℕ)
    (ins : ∀t,Installed F groups ports lanes w m (key t).2 (atScale positive stage (key t).1 raw))
    (freeCap : {i : Fin nRows // ¬positive i}→ℕ)
    (ord : Pin (banks ins) freeCap (Fin ((es.length+1)*Fintype.card ((u : Public S h W k attempts) × Fin (cap u)))) ((Fin groups×Fin ports)×Fin view) ≃ D)

include packing in
/-- Actual fixed entry network at the same shared voltages used by the
purchased bank contraction, including its genuine initial time slice. -/
theorem first_native (a : ∀i,Fin (2^(raw i).width)) (z : SiteChoices slot wire es x j) (s : Fin N)
    (external : Ex→Bool) (sel : Se→Bool) (seen : B.Seen→Bool) :
    TypedWiring.value (firstNetwork S cap es B (timePin ord) extPort F s)
      (PhysicalTerm.CalendarTerms.readPins ord external sel seen
        (nativePins (view:=view) key raw positive stage ins freeCap a
          (placedBits slot wire es x j (timelineFin slot wire cells es x j) z)))=
      PhysicalTerm.entry π wire x head s (fun i=>external (extPort i.val)) (z s).1 := by
  let pins := nativePins (view:=view) key raw positive stage ins freeCap a
    (placedBits slot wire es x j (timelineFin slot wire cells es x j) z)
  change TypedWiring.value _ (PhysicalTerm.CalendarTerms.readPins (B:=B) (Equiv.refl D)
    external sel seen (pins ∘ ord.symm))=_
  apply first_value S π depth marked unique rows cap room slot wire cells es x j head packing B (timePin ord) extPort z s external sel seen
  intro t
  change pins (ord.symm (ord (.inr (.inr (.inl t)))))=_
  rw [ord.symm_apply_apply]
  rfl

end Contracted

end Hierarchy.ProbeStage.CoreBoard.EntryOrder
end

end OAI
