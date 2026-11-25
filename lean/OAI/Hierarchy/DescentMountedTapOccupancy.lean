import OAI.Hierarchy.DescentMountedContactKey
import OAI.Hierarchy.DescentRotorArgumentCoverage

namespace OAI
namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentRouterSlots DescentBatchedBank DescentBundleHistory DescentRetainedRangeDigits DescentBatchedNodeOrder
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
open private transportCircuit from OAI.Hierarchy.DescentInstalledNames
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
    {k n h C₀ bits u N : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
    (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
    (key : I↪Fin N) (D m p : ℕ) (hp : 0<p) (fit : u=m*p)
variable (s : Bool) (g : P.Good)
local notation "sizedHardware" => (fit ▸ hardware : Hardware (K:=K) (C₀:=C₀) (u:=m*p) P G hw pay)
local notation "sizedChoice" => selected P G hw pay sizedHardware s (.inl g)
local notation "trueDevice" => DescentMixedRouter.device G hw (m*p) P.contact P.input P.site P.owner P.align
  (D:=D) sizedChoice
open DescentLaneGates

local notation "itemEnum" => @Subtype.fintype I (fun a => P.owner s (P.contact a) = Sum.inl g)
  (fun _ => Classical.propDecidable _) inferInstance
local notation "base" => (transportCircuit (b:=itemEnum) (G:=G) (hw:=hw) (pay:=pay) (sizedHardware s g))

open DescentPhysicalSplit DescentLaneGates
set_option quotPrecheck false
local notation "H₀" => Physical.host G.arcs D (selectedRotorLayers P G hw pay sizedHardware s g) C₀ bits (m*p)
local notation "tapLeg" => DescentResetGates.tapLegLane D (m*p) P.contact P.input P.site P.owner P.align s
  (.inl g) G (head P s g) (tail P s g) base key (m:=m) (p:=p) rfl hp
variable (vertex : Fin (2^n))
variable (i : Fin (DescentPhysicalSplit.count (Physical.host G.arcs D
  (selectedRotorLayers P G hw pay (fit ▸ hardware : Hardware (K:=K) (C₀:=C₀) (u:=m*p) P G hw pay) s g)
  C₀ bits (m*p)) vertex))
local notation "rawTap" => (⟨vertex,.inr i⟩ : (trueDevice).Site)
local notation "tapWidth" => boundaryWidth trueDevice rawTap
local notation "tapUnits" => (fun e=>tapWidth e/p)
local notation "pub" => DescentResetGates.publicTapLane D (m*p) P.contact P.input P.site P.owner P.align s
  (.inl g) G (head P s g) (tail P s g) base key (m:=m) (p:=p) rfl hp
local notation "legBits_" => @DescentResetGates.legBits (Cells P s g) K itemEnum _ D (m*p) n h bits C₀ G hw pay _ _ base
local notation "color" => DescentLaneGates.Block (selectedRotorLayers P G hw pay sizedHardware s g) m
  (@DescentResetGates.tapBits (Cells P s g) K itemEnum _ D (m*p) n h bits C₀ G hw pay _ _ base vertex i)

local instance (priority := high) occupancyCellsEnum : Fintype (Cells P s g) := itemEnum

open DescentPhysicalSplit DescentResetLaneIssue DescentResetPublicOperandBook DescentRotorOperandQueryROM.Shape
open private DescentChosenRouter.cast_leg from OAI.Hierarchy.DescentMountedContactKey

local notation "src" => (fun e : Cells P s g => (head P s g) (DescentRouterSlots.root P.contact P.input P.site P.owner s (.inl g) P.align e))
local notation "dst" => (fun e : Cells P s g => (tail P s g) (DescentRouterSlots.link P.contact P.owner s (.inl g) e))
local notation "pick" => (Function.Embedding.subtype (fun e=>P.owner s (P.contact e)=.inl g)).trans key
local notation "array" => DescentRotor.Ordered.orderedAddress pick src dst hw
local notation "idx" t:arg slot:arg => (t).2.2.cast (congrArg legBits_ slot)
local notation "mouth" pin:arg q:arg t:arg slot:arg offset:arg => (⟨pin,q,(t).1.val,(t).2.1.val,(idx t slot).val,offset⟩ : Mouth n)
local notation "group_" pin:arg q:arg => DescentRotorOperandRanks.At src dst (fun z=>(if pin then z.2 else z.1)=q)

/-- An actual live argument supplies an occupied rail, and its typed index is
below the chronological cover at that same physical tap. -/
theorem mounted_live_tap (q : Fin (2^n)) (pin : Bool) (slot : name H₀ vertex i=.inl (q,pin))
    (t : color) (lane : Lane p tapWidth) (within : Fin (lane.count tapUnits))
    (onGate : tapLeg vertex i t.1 t.2.1 t.2.2=.wire lane) :
    ∃e : Cells P s g,((if pin then dst e else src e)=q ∧ (base).choose (array e).1=t.1 ∧ (array e).2=idx t slot) ∧
      within.val< min 2 (Fintype.card (group_ pin q)*m-
        (Config.earlierCount src dst pick (mouth pin q t slot within.val) e*m+t.2.1.val)) :=by
  let placed:=(congrArg (tap H₀) slot).symm.trans (tap_named H₀ vertex i)
  have atPort : Eq.ndrec (motive:=fun a=>LaneSource p (boundaryWidth trueDevice a))
      (pub pin q t.1 t.2.1 (idx t slot)) placed=.wire lane:=by
    exact (DescentChosenRouter.cast_leg P G hw pay hardware key D m p hp fit s g vertex i _ _ slot (tap_named H₀ vertex i)
      t.2.2 t.1 t.2.1).symm.trans onGate
  have view (a b : (trueDevice).Site) (loc : a=b) (source : LaneSource p (boundaryWidth trueDevice a))
      (chosen : Lane p (boundaryWidth trueDevice b))
      (control : (loc ▸ source : LaneSource p (boundaryWidth trueDevice b))=.wire chosen) :
      ∃old : Lane p (boundaryWidth trueDevice a),source=.wire old ∧
        old.count (fun z=>boundaryWidth trueDevice a z/p)=chosen.count (fun z=>boundaryWidth trueDevice b z/p) :=by
    cases loc
    exact ⟨chosen,control,rfl⟩
  obtain ⟨old,live,size⟩:=view _ _ placed _ lane atPort
  have occupied : ∃e : Cells P s g,(if pin then dst e else src e)=q ∧
      (base).choose (array e).1=t.1 ∧ (array e).2=idx t slot:=by
    by_contra none
    obtain ⟨value,fixed⟩:=public_lane_vacant D m p hp P.contact P.input P.site P.owner P.align s (.inl g) G
      (head P s g) (tail P s g) (base) key pin q t.1 t.2.1 (idx t slot) none
    cases fixed.symm.trans live
  obtain ⟨e,chosen⟩:=occupied
  obtain ⟨_,extent⟩:=public_focus_word D m p hp P.contact P.input P.site P.owner P.align s (.inl g) G
    (head P s g) (tail P s g) (base) key pin q t.1 t.2.1 (idx t slot) within.val e chosen old live
  exact ⟨e,chosen,lt_of_lt_of_eq within.isLt (size.symm.trans extent)⟩

end
end Hierarchy.DescentChosenRouter

end OAI
