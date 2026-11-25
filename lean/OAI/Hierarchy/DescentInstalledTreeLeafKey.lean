import OAI.Hierarchy.DescentFallbackLeafBlock
import OAI.Hierarchy.DescentNumberedFallbackKeys

namespace OAI
/-! The original contact slot in both signs of the installed exceptional tree. -/
namespace Hierarchy.DescentBatchedBank
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRouterSlots
noncomputable section
set_option quotPrecheck false
variable {I C R W : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W]
  (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W) (weight : I→ℕ)
local notation "N" => DescentRouterBank.network D contact input site owner weight
omit [Fintype R] in
theorem installed_link_slot {d : ℕ} (components : ∀v,Network d (DescentNetworkSubstitution.Slot N v)
    (DescentNetworkSubstitution.slotWidth N v)) (s : Bool) (w : W) (q : (components (s,w)).Site)
    (a : Boundary (components (s,w)) q) (c : LinkId owner s w)
    (selected : Sum.map Subtype.val Subtype.val a=.inr (linkSlot D contact input site owner weight s w c)) :
    Sum.map Subtype.val Subtype.val ((portMap N components (s,w) q).slot a)=.inl (.inl c.val) :=by
  rcases a with edge|⟨slot,attached⟩
  · cases selected
  · have same : slot=linkSlot D contact input site owner weight s w c:=Sum.inr.inj selected
    subst slot
    cases s <;> rfl
open private DescentNetworkSubstitution.sourceTap_at DescentNetworkSubstitution.targetTap_at from
  OAI.Hierarchy.DescentNetworkSubstitution

omit [Fintype R] in
theorem installed_link_end {d : ℕ} (components : ∀v,Network d (DescentNetworkSubstitution.Slot N v)
    (DescentNetworkSubstitution.slotWidth N v)) (s : Bool) (w : W) (q : (components (s,w)).Site)
    (a : Boundary (components (s,w)) q) (c : LinkId owner s w)
    (selected : Sum.map Subtype.val Subtype.val a=.inr (linkSlot D contact input site owner weight s w c)) :
    (if s then (DescentNetworkSubstitution.network N components).dst (.inl c.val)
      else (DescentNetworkSubstitution.network N components).src (.inl c.val))=⟨(s,w),q⟩ :=by
  rcases a with edge|⟨slot,attached⟩
  · cases selected
  · have same : slot=linkSlot D contact input site owner weight s w c:=Sum.inr.inj selected
    subst slot
    cases s
    · exact (DescentNetworkSubstitution.sourceTap_at N components ⟨c.val,congrArg (Prod.mk false) c.property⟩).trans
        (congrArg (Sigma.mk (false,w)) attached)
    · exact (DescentNetworkSubstitution.targetTap_at N components ⟨c.val,congrArg (Prod.mk true) c.property⟩).trans
        (congrArg (Sigma.mk (true,w)) attached)

end
end Hierarchy.DescentBatchedBank

namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentContactTree DescentRouterSlots DescentOrderedWords DescentBatchedBank DescentBundleHistory
open DescentRetainedRangeDigits DescentPhysicalSplit
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
variable {k n h C₀ bits u N : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
  (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
  (key : I↪Fin N) (D m p : ℕ) (hp : 0<p) (fit : u=m*p)
local notation "selection" => selected P G hw pay hardware
local notation "bank" => DescentMixedRouter.network G hw u P.contact P.input P.site P.owner P.align selection D
local notation "programAt" => sizedProgram G hw u m p hp fit P.contact P.input P.site P.owner P.align key D selection
local notation "ord" => DescentBatchedNodeOrder.sizedOrder G hw m p hp P.contact P.input P.site P.owner P.align key D u fit selection
variable (s : Bool) (t : H)
local notation "book" => P.fallbackBook s t
local notation "code" => DescentFixedNamedContact.code (book).codes (link P.contact P.owner s (.inr t))
local notation "ids" => DescentOrderedReset.itemKey key P.contact P.owner s (.inr t)

variable (e : Item P.contact P.owner s (.inr t)) (b : Fin m)
local notation "q" => (⟨Fin.last (book).height,prefixAt code (book).height e⟩ : Physical.Site (book).height)
local notation "venue" => (⟨(s,.inr t),q⟩ : (bank).Site)
local notation "outer" => DescentRouterBank.network D P.contact P.input P.site P.owner (fun _ : I => m*p)
local notation "components" mounted => (fun a : (outer).Site =>
  DescentMixedRouter.device (K:=K) (C₀:=C₀) G hw (m*p) P.contact P.input P.site P.owner P.align
    (D:=D) (selected P G hw pay mounted a.1 a.2))
local notation "raw" => DescentFixedExceptionalRouter.device D P.contact P.input P.site P.owner (fun _ : I=>m*p) s (.inr t) (book).codes
local notation "rawOp" => DescentTreeLaneProgram.program D P.contact P.input P.site P.owner P.align m p hp s (.inr t) (book).codes key (2^n) q
local notation "right" => (((rawOp).op (⟨e,rfl⟩,b)).arg (1 : Fin 2))
local notation "units" => (fun a=>boundaryWidth raw q a/p)
set_option maxHeartbeats 1200000 in
theorem installed_leaf_block (multiple : ∀a,boundaryWidth raw q a=units a*p) (j : Fin ((right).count units)) :
    let r:=laneBlock units multiple hp right j
    let out:=(installedTreePorts P G hw pay hardware D m p fit s t q).wordBlock r
    Sum.map Subtype.val Subtype.val out.port=.inl (.inl (P.contact e.val)) ∧
      out.block=(right).bundleStart+j.val ∧ out.block/m<Fintype.card (DescentNamedContact.Fibre P.contact (P.contact e.val)) :=by
  subst u
  intro r out
  obtain ⟨atPin,word,within⟩:=DescentTreeLaneProgram.leaf_contact_block D P.contact P.input P.site P.owner P.align m p hp
    s (.inr t) (book).codes key (2^n) e b multiple j
  have cards (i j : Fintype (DescentNamedContact.Fibre P.contact (P.contact e.val))) :
      @Fintype.card _ i = @Fintype.card _ j :=
    @Fintype.card_congr _ _ i j (Equiv.refl _)
  exact ⟨DescentBatchedBank.installed_link_slot D P.contact P.input P.site P.owner (fun _=>m*p)
    (components hardware) s (.inr t) q r.port (link P.contact P.owner s (.inr t) e) atPin, word,
    lt_of_lt_of_eq within (cards _ _)⟩

set_option maxHeartbeats 1200000 in
include key m p hp fit b in
theorem installed_leaf_end :
    (if s then (bank).dst (.inl (P.contact e.val)) else (bank).src (.inl (P.contact e.val)))=venue :=by
  subst u
  have laneFields:=DescentTreeLaneProgram.following_fields D P.contact P.input P.site P.owner P.align m p hp
    s (.inr t) (book).codes key (2^n) e b (Fin.last (book).height)
  simp only [Fin.lastCases_last] at laneFields
  exact DescentBatchedBank.installed_link_end D P.contact P.input P.site P.owner (fun _=>m*p)
    (components hardware) s (.inr t) q (right).port (link P.contact P.owner s (.inr t) e) (congrArg Prod.fst laneFields)

end
end Hierarchy.DescentChosenRouter

end OAI
