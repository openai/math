import OAI.Hierarchy.TaggedWireEntryNative

namespace OAI
/-! # Every actual first party state is recovered from its placed public words -/

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
private def placedVector {N : ℕ} {H : Type*} {A B : Widths N} (cap : H→ℕ)
    (place : (Σ s,SiteBit A s) ↪ (Σ q,Fin (cap q))) (eq : A=B)
    (state : ∀s,State B s) (socket : H) (index : ℕ) : Bool :=
  if bounded:index<cap socket then
    Function.extend place (fun a=>siteBits B a.1 (state a.1) (NamedAperture.transportAt eq a.2))
      (fun _=>false) ⟨socket,⟨index,bounded⟩⟩
  else false

private theorem placed_read {N : ℕ} {H : Type*} {A B : Widths N} (cap : H→ℕ)
    (place : (Σ s,SiteBit A s) ↪ (Σ q,Fin (cap q))) (eq : A=B)
    (state : ∀s,State B s) (a : Σ s,SiteBit A s) :
    placedVector cap place eq state (place a).1 (place a).2.val=
      siteBits B a.1 (state a.1) (NamedAperture.transportAt eq a.2) := by
  unfold placedVector
  rw [dite_eq_left (place a).2.isLt]
  exact place.injective.extend_apply _ _ a

def vector (room : InitialRoom S p depth marked unique rows cap w R)
    (state : ∀s,State (exposedWidth p (2^W) k w R) s) : Public S h W k epochs→ℕ→Bool :=
  placedVector cap (NamedAperture.place (edges rows) (amount rows) (named S p.symm depth marked unique rows) cap room)
    (source_aggregate (w:=w) (R:=R) S p depth marked rows) state

variable (room : InitialRoom S p depth marked unique rows cap w R)
variable (state : ∀s,State (exposedWidth p (2^W) k w R) s)

private theorem cancel {N : ℕ} {A B : Widths N} (eq : A=B) {s : Fin N} (u : SiteBit B s) :
    NamedAperture.transportAt eq (NamedAperture.transportAt eq.symm u)=u := by subst B;rfl

theorem state_read (s : Fin (siteLast h (2^W) k+1)) :
    initialState S p depth marked unique rows cap room (vector S p depth marked unique rows cap room state) s=state s := by
  apply (siteBits U s).injective
  funext u
  let eq:=source_aggregate (w:=w) (R:=R) S p depth marked rows
  let place:=NamedAperture.place (edges rows) (amount rows) (named S p.symm depth marked unique rows) cap room
  let old : Σt,SiteBit (installedWidths (edges rows) (amount rows)) t:=⟨s,NamedAperture.transportAt eq.symm u⟩
  let loc:=place old
  have read : vector S p depth marked unique rows cap room state loc.1 loc.2.val=
     siteBits U s (state s) (NamedAperture.transportAt eq (NamedAperture.transportAt eq.symm u)) :=
    placed_read cap place eq state old
  simp only [initialState,Equiv.apply_symm_apply]
  apply read.trans
  exact congrArg _ (cancel eq u)

theorem fixed_on_state (F : Type*) [Field F] (s : Fin (siteLast h (2^W) k+1)) (x : {i // τ i=s}→Bool) :
    TypedWiring.value (MatchingEntry.fixedNetwork τ F s)
      (fixedPins S (vector S p depth marked unique rows cap room state) x)=exposedMatrix p (2^W) k w R s x (state s) := by
  rw [fixed_read S p depth marked unique rows cap room _ F s x,state_read]

end Hierarchy.ProbeStage.CoreBoard.EntryOrder
end

end OAI
