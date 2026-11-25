import OAI.Hierarchy.DescentOriginalRotorCount
import OAI.Hierarchy.DescentMountedGoodNode
import OAI.Hierarchy.DescentInstalledNames
import OAI.Hierarchy.DescentInstalledLaneRange

namespace OAI
/-! # The physical good-bank instruction, its ordinal and its exact range in the installed reset -/
namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentRouterSlots DescentBatchedBank DescentBundleHistory DescentRetainedRangeDigits DescentBatchedNodeOrder
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
    {k n h C₀ bits u N : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
    (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
    (key : I↪Fin N) (D m p : ℕ) (hp : 0<p) (fit : u=m*p)
local notation "sel" => selected P G hw pay hardware
local notation "bank" => DescentMixedRouter.network G hw u P.contact P.input P.site P.owner P.align sel D
local notation "prg" => sizedProgram G hw u m p hp fit P.contact P.input P.site P.owner P.align key D sel
variable (s : Bool) (g : P.Good)
local notation "r" => (⟨s,.inl g⟩ : Bool×P.Site)
local notation "sizedHardware" => (fit ▸ hardware : Hardware (K:=K) (C₀:=C₀) (u:=m*p) P G hw pay)
local notation "sizedChoice" => selected P G hw pay sizedHardware s (.inl g)
local notation "trueDevice" => DescentMixedRouter.device G hw (m*p) P.contact P.input P.site P.owner P.align
  (D:=D) sizedChoice
local notation "installedSite" => DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay hardware s g) C₀ bits u
local notation "sizedSite" => DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay sizedHardware s g) C₀ bits (m*p)
local notation "prog" v => (DescentBatchedBank.deviceProgram G hw m p hp P.contact P.input P.site P.owner
  P.align key D sizedChoice (sizedSite v))
local notation "widthAt" v => (boundaryWidth trueDevice (sizedSite v))
local notation "venue" v => (⟨r,installedSite v⟩ : (bank).Site)
variable (v : (DescentCommonPalette.rotor G).Site)
local notation "μ" => (fun i => (widthAt v) i / p)

open DescentLaneGates
-- These are the actual rack and its selected devices once the unit is substituted.
local notation "rack" => DescentRouterBank.network D P.contact P.input P.site P.owner (fun _ : I=>m*p)
local notation "fixedCell" c => (DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay c s g) C₀ bits (m*p) v)
local notation "fixedPorts" c => (portMap rack (fun a : (rack).Site =>
  DescentMixedRouter.device G hw (m*p) P.contact P.input P.site P.owner P.align (D:=D)
    (selected P G hw pay c a.1 a.2)) r (fixedCell c))
theorem mountedGoodRange
    (multiple : ∀e,boundaryWidth bank (venue v) e=boundaryWidth bank (venue v) e/p*p)
    (node : (prg (venue v)).Node) :
    ∃ localMultiple : ∀e,(widthAt v) e=μ e*p,
    ∀arg f,
      atSlot (ofProgram (fun i=>boundaryWidth bank (venue v) i/p) multiple hp (prg (venue v))) node arg f=
        atSlot (ofProgram μ localMultiple hp (prog v)) (mountedGoodNode P G hw pay hardware key D m p hp fit s g v node) arg f:=by
  revert hardware multiple node
  subst u
  intro mounted multiple node
  refine ⟨before_multiple (fixedPorts mounted) multiple, ?_⟩
  intro arg f
  exact DescentBatchedBank.installed_range G hw m p hp P.contact P.input P.site P.owner P.align key D
    (selected P G hw pay mounted) (⟨(s,.inl g),fixedCell mounted⟩) multiple node arg f

end
end Hierarchy.DescentChosenRouter

end OAI
