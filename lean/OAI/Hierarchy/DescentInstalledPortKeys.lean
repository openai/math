import OAI.Hierarchy.DescentLanePortKeys
import OAI.Hierarchy.DescentInstalledLaneRange

namespace OAI
namespace Hierarchy.DescentBatchedBank
open DescentBundleHistory DescentRetainedRangeDigits DescentLaneGates
open Computability.BorderVNP.Crossing DescentRotor DescentKernelHistory DescentResetGates DescentMixedRouter
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits M : ℕ} (G : Graph n h) (hw : 0<bits) (u m p : ℕ) (hp : 0<p) (fit : u=m*p)
variable (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (key : I↪Fin M) (D : ℕ)
variable (select : ∀s w,Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align s w)
local notation "bank" => DescentMixedRouter.network G hw u contact input site owner align select D
local notation "rack" => DescentRouterBank.network D contact input site owner (fun _ : I=>u)
local notation "devices" => fun a : (rack).Site=>device G hw u contact input site owner align (D:=D) (select a.1 a.2)
local notation "pAt" => sizedProgram G hw u m p hp fit contact input site owner align key D select

local notation "old" => sizedLocal G hw u m p hp fit contact input site owner align key D select


omit [Fintype R] in
theorem sized_key (v : (bank).Site) (mul : ∀i,boundaryWidth bank v i=boundaryWidth bank v i/p*p)
    (t : (pAt v).Node) (arg : ℕ) (r : BlockRef p (boundaryWidth (devices v.1) v.2))
    (localMul : ∀a,boundaryWidth (devices v.1) v.2 a=boundaryWidth (devices v.1) v.2 a/p*p)
    (hit : ((ofProgram (fun j=>boundaryWidth (devices v.1) v.2 j/p) localMul hp (old v)).keys
      (sizedLocalNode G hw u m p hp fit contact input site owner align key D select v t))[arg]?=some (.inl r)) :
    ((ofProgram (fun j=>boundaryWidth bank v j/p) mul hp (pAt v)).keys t)[arg]?=
      some (.inl ((portMap rack devices v.1 v.2).wordBlock r)) :=by
  subst u
  let raw := DescentRouterBank.network D contact input site owner (fun _ : I => m*p)
  let localDevice := fun a : raw.Site =>
    device G hw (m*p) contact input site owner align (D:=D) (select a.1 a.2)
  exact (portMap raw localDevice v.1 v.2).transported_key localMul mul hp
    (deviceProgram G hw m p hp contact input site owner align key D (select v.1.1 v.1.2) v.2) t arg r hit

end
end Hierarchy.DescentBatchedBank

namespace Hierarchy.DescentSixParty.ResetInput
open DescentBundleHistory DescentRetainedRangeDigits DescentBatchedBank
open Computability.BorderVNP.Crossing DescentRotor DescentChosenRouter DescentKernelHistory DescentResetGates
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht L : ℕ} (Z : ResetInput A price ε h C Ht) (key : A.graph.Edge↪Fin L)
variable (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
local notation "R" => Z.placement
local notation "chosen" => DescentChosenRouter.selected R Z.graph Z.positive Z.pay Z.circuit

local notation "rack" => DescentRouterBank.network d (R).contact (R).input (R).site (R).owner (fun _ : A.graph.Edge=>Z.unit)
local notation "devices" => fun u : (rack).Site=>DescentMixedRouter.device Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align (D:=d) (chosen u.1 u.2)
local notation "localProgram" => sizedLocal Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen
local notation "nodes" => sizedLocalNode Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen


def bankPorts (v : Z.bank.Site) : DescentLaneGates.PortMap (boundaryWidth (devices v.1) v.2)
    (boundaryWidth Z.bank v) :=portMap rack devices v.1 v.2

/-- The actual installer applies its boundary substitution to each local
rotor or tree operand. The aligned word number survives unchanged. -/
theorem bank_laneBlock (v : Z.bank.Site) (t : (Z.laneRecipe key m p hp fit v).Node)
    (arg : ℕ) (r : BlockRef p (boundaryWidth (devices v.1) v.2))
    (localMul : ∀a,boundaryWidth (devices v.1) v.2 a=boundaryWidth (devices v.1) v.2 a/p*p)
    (hit : ((ofProgram (fun a=>boundaryWidth (devices v.1) v.2 a/p) localMul hp (localProgram v)).keys
      (nodes v t))[arg]?=some (.inl r)) :
    ((Z.laneShape key m p hp fit v).keys t)[arg]?=some (.inl ((Z.bankPorts v).wordBlock r)) :=
  sized_key Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen
    v (Z.laneWidth_eq m p fit v) t arg r localMul hit

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
