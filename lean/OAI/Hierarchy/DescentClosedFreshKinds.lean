import OAI.Hierarchy.DescentMountedGoodNode
import OAI.Hierarchy.DescentNumberedFallbackNode

namespace OAI
/-! # Every installed reset gate has its actual rotor or tree ordinal -/
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
variable (s : Bool) (t : H)
local notation "book" => P.fallbackBook s t
local notation "code" => DescentFixedNamedContact.code (book).codes (link P.contact P.owner s (.inr t))
variable (q : Physical.Site (P.fallbackBook s t).height)
local notation "venue" => (⟨(s,.inr t),q⟩ : (bank).Site)

/-- The tree device installs precisely one gate per actual tree cell and batch. -/
theorem installedTreeGate_onto (node : (programAt venue).Node) :
    ∃ (e : Cell code q.1.val q.2) (batch : Fin m),
      installedTreeGate P G hw pay hardware key D m p hp fit s t q e batch=node :=by
  subst u
  exact ⟨node.1,node.2,rfl⟩

end
end Hierarchy.DescentChosenRouter

namespace Hierarchy.DescentSixParty.ResetInput
open Computability.BorderVNP.Crossing DescentChosenRouter DescentOrderedWords DescentContactTree DescentRouterSlots
open DescentKernelHistory DescentRetainedRangeDigits DescentBundleHistory
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d N : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (key : A.graph.Edge↪Fin N)
variable (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
local notation "atSite" => Z.laneProgram key m p hp fit
local notation "gatePair" => (Σ v : Z.bank.Site, (atSite v).Node)
local notation "R" => Z.placement
local notation "sizedHardware" => (fit ▸ Z.circuit : Hardware (K:=F) (C₀:=C) (u:=m*p) R Z.graph Z.positive Z.pay)
local notation "installedSite" s:arg g:arg => DescentCommonPalette.rotorSiteEquiv Z.graph d
  (selectedRotorLayers R Z.graph Z.positive Z.pay Z.circuit s g) C Z.width Z.unit
local notation "sizedSite" s:arg g:arg => DescentCommonPalette.rotorSiteEquiv Z.graph d
  (selectedRotorLayers R Z.graph Z.positive Z.pay sizedHardware s g) C Z.width (m*p)
local notation "goodVenue" s:arg g:arg a:arg => (⟨(s,.inl g), (installedSite s g) a⟩ : Z.bank.Site)
local notation "fallVenue" s:arg t:arg a:arg => (⟨(s,.inr t),a⟩ : Z.bank.Site)
local notation "sizedChoice" s:arg g:arg => selected R Z.graph Z.positive Z.pay sizedHardware s (.inl g)
local notation "goodProgram" s:arg g:arg => DescentBatchedBank.deviceProgram Z.graph Z.positive
  m p hp (R).contact (R).input (R).site (R).owner (R).align key d (sizedChoice s g)
local notation "goodOrder" s:arg g:arg => DescentBatchedNodeOrder.deviceOrder Z.graph Z.positive
  m p hp (R).contact (R).input (R).site (R).owner (R).align key d (sizedChoice s g)
local notation "goodNode" => mountedGoodNode R Z.graph Z.positive Z.pay Z.circuit key d m p hp fit
local notation "treeNode" => installedTreeGate R Z.graph Z.positive Z.pay Z.circuit key d m p hp fit
local notation "codes" s:arg t:arg => ((R).fallbackBook s t).codes
local notation "treeCode" s:arg t:arg => DescentFixedNamedContact.code (codes s t) (link (R).contact (R).owner s (.inr t))
local notation "treeKey" s:arg t:arg => DescentOrderedReset.itemKey key (R).contact (R).owner s (.inr t)

set_option maxHeartbeats 1200000

/-- The original mounted gate, together with its printed local number. -/
def MountedAt (x : gatePair) (number : ℕ) : Prop :=
    (∃ (s : Bool) (g : (R).Good) (a : (DescentCommonPalette.rotor Z.graph).Site)
       (u : ((goodProgram s g) ((sizedSite s g) a)).Node),
       x=⟨goodVenue s g a, (goodNode s g a).symm u⟩ ∧
         number=(((goodOrder s g) ((sizedSite s g) a)) u).val) ∨
    (∃ (s : Bool) (t : Z.Fallback) (q : Physical.Site ((R).fallbackBook s t).height)
       (e : Cell (treeCode s t) q.1.val q.2) (batch : Fin m),
       x=⟨fallVenue s t q,treeNode s t q e batch⟩ ∧
         number=
           (before (Contact.cellKey (treeKey s t) (treeCode s t) q.1.val q.2) e).card*m+batch.val)

/-- Split any mounted dependent pair, retaining every rotor instruction and tree batch. -/
theorem closed_fresh_kinds (v : Z.bank.Site) (node : (atSite v).Node) :
    Z.MountedAt key m p hp fit ⟨v,node⟩ (Z.nodeIndex key m p hp fit v node) :=by
  unfold MountedAt
  rcases v with ⟨⟨s,g|t⟩,a⟩
  · obtain ⟨a, rfl⟩ := (installedSite s g).surjective a
    refine Or.inl ⟨s,g,a,goodNode s g a node,?_,?_⟩
    · exact congrArg (fun n => (⟨goodVenue s g a, n⟩ : gatePair))
        ((goodNode s g a).symm_apply_apply node).symm
    · exact mountedGoodIndex R Z.graph Z.positive Z.pay Z.circuit key d m p hp fit s g a node
  · obtain ⟨e,batch,he⟩ := installedTreeGate_onto R Z.graph Z.positive Z.pay Z.circuit
      key d m p hp fit s t a node
    subst node
    exact Or.inr ⟨s,t,a,e,batch,rfl,
      installedTreeIndex R Z.graph Z.positive Z.pay Z.circuit key d m p hp fit s t a e batch⟩

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
