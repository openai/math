import OAI.Hierarchy.DescentInstalledRotorLayers
import OAI.Hierarchy.DescentRotorPhysicalMaps
import OAI.Hierarchy.DescentBatchedNodeOrder

namespace OAI
/-! # The original local ordinal in a mounted rotor cell -/
namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentRouterSlots DescentBatchedBank DescentBatchedNodeOrder
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
    {k n h C₀ bits u N : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
    (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
    (key : I↪Fin N) (D m p : ℕ) (hp : 0<p) (fit : u=m*p)
local notation "sel" => selected P G hw pay hardware
local notation "bank" => DescentMixedRouter.network G hw u P.contact P.input P.site P.owner P.align sel D
local notation "prg" => sizedProgram G hw u m p hp fit P.contact P.input P.site P.owner P.align key D sel
local notation "ord" => sizedOrder G hw m p hp P.contact P.input P.site P.owner P.align key D u fit sel
variable (s : Bool) (g : P.Good)
local notation "r" => (⟨s,.inl g⟩ : Bool×P.Site)
local notation "sizedHardware" => (fit ▸ hardware : Hardware (K:=K) (C₀:=C₀) (u:=m*p) P G hw pay)
local notation "sizedChoice" => selected P G hw pay sizedHardware s (.inl g)
local notation "installedSite" => DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay hardware s g) C₀ bits u
local notation "sizedSite" => DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay sizedHardware s g) C₀ bits (m*p)
local notation "prog" => DescentBatchedBank.deviceProgram G hw m p hp P.contact P.input P.site P.owner P.align key D sizedChoice
local notation "number" => deviceOrder G hw m p hp P.contact P.input P.site P.owner P.align key D sizedChoice
local notation "venue" v => (⟨r,installedSite v⟩ : (bank).Site)
variable (v : (DescentCommonPalette.rotor G).Site)

/-- Substituting the true stage unit transports the label, preserving the local
ordinal within the original device. All public and private occurrences remain
the ones in the mounted program. -/
def mountedGoodNode : (prg (venue v)).Node ≃ (prog (sizedSite v)).Node:=by
  subst u
  exact Equiv.refl _

theorem mountedGoodIndex (node : (prg (venue v)).Node) :
    (ord (venue v) node).val=(number (sizedSite v) (mountedGoodNode P G hw pay hardware key D m p hp fit s g v node)).val:=by
  subst u
  rfl

end
end Hierarchy.DescentChosenRouter

end OAI
