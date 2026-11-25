import OAI.Hierarchy.DescentBatchedBank
import OAI.Hierarchy.DescentResetWorldHistory
import OAI.Hierarchy.DescentResetQuantum

namespace OAI
/-! # The installed reset's unit-width receipt yields its actual powered bit history -/

namespace Hierarchy.DescentBatchedBank
open Computability.BorderVNP.Crossing DescentRotor DescentKernelHistory DescentResetGates DescentMixedRouter
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits M : ℕ} (G : Graph n h) (hw : 0<bits) (u m p : ℕ) (hp : 0<p) (fit : u=m*p)
variable (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (key : I↪Fin M) (D : ℕ)
variable (select : ∀s w,Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align s w)
local notation "bank" => DescentMixedRouter.network G hw u contact input site owner align select D
local notation "coeff" => DescentMixedRouter.Ordered.coefficients G hw u contact input site owner align key D select

include fit hp key in
def sizedProgram (v : (bank).Site) : DescentLaneGates.Program (2^n) p (boundaryWidth bank v) := by
  subst u
  exact program G hw m p hp contact input site owner align key D select v

local notation "atSite" => sizedProgram G hw u m p hp fit contact input site owner align key D select

theorem sized_count (v : (bank).Site) : Fintype.card (atSite v).Node*p≤2*DescentNetworkSubstitution.portLoad bank v := by
  subst u
  exact node_count_mul_le G hw m p hp contact input site owner align key D select v

omit [Fintype R] in
theorem sized_arity (v : (bank).Site) (t : (atSite v).Node) : ((atSite v).op t).arity≤ max 2 ((2+2*h*C₀)*bits) := by
  subst u
  exact arity_bound G hw m p hp contact input site owner align key D select v t

omit [Fintype R] in
theorem sized_stride (v : (bank).Site) (t : (atSite v).Node) (j : Fin ((atSite v).op t).arity) :
    (((atSite v).op t).arg j).stride≤ max 1 (max bits (C₀*bits)) := by
  subst u
  exact stride_bound G hw m p hp contact input site owner align key D select v t j

variable (menu : ∀π,Configures K G.arcs C₀ bits π)
local notation "evalAt" => DescentLaneGates.scalar G.arcs C₀ bits p (rom G.arcs C₀ bits (fixedTable menu))

omit [Fintype R] in
theorem sized_read : ReadsBits bank evalAt (fun v=>(atSite v).recipe) coeff := by
  subst u
  intro a x v
  let N:=DescentMixedRouter.network G hw (m*p) contact input site owner align select D
  have same : bitInput N a x v=assignmentBit N a x v := by funext z;rcases z with ⟨_|_,j⟩ <;> rfl
  rw [same]
  exact program_read G hw m p hp contact input site owner align key D menu select a x v
end
end Hierarchy.DescentBatchedBank

namespace Hierarchy.DescentSixParty.ResetInput
open Computability.BorderVNP.Crossing DescentRotor DescentChosenRouter DescentKernelHistory DescentResetGates
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht L : ℕ} (Z : ResetInput A price ε h C Ht) (key : A.graph.Edge↪Fin L)
variable (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
local notation "R" => Z.placement
local notation "chosen" => DescentChosenRouter.selected R Z.graph Z.positive Z.pay Z.circuit

include key hp fit in
def laneProgram (v : Z.bank.Site) : DescentLaneGates.Program (2^Z.n) p (boundaryWidth Z.bank v) :=
  DescentBatchedBank.sizedProgram Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen v

include key hp fit in
def laneRecipe : SiteBits (U:=CanonicalTag (2^Z.n)) Z.bank := fun v=>(Z.laneProgram key m p hp fit v).recipe

include fit in
/-- Each true incident wire or original exterior terminal is an integral number of p-bit lanes. -/
theorem lane_dvd (v : Z.bank.Site) (r : Boundary Z.bank v) : p∣boundaryWidth Z.bank v r := by
  have per : p∣Z.unit:=⟨m,fit.trans (Nat.mul_comm _ _)⟩
  rcases r with e|pin
  · exact per.trans (DescentMixedRouter.quantum Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align chosen e.val)
  · exact per.trans (DescentMixedRouter.public_quantum Z.unit (R).input pin.val)

include fit in
theorem laneWidth_eq (v : Z.bank.Site) (r : Boundary Z.bank v) :
    boundaryWidth Z.bank v r=(boundaryWidth Z.bank v r/p)*p := (Nat.div_mul_cancel (Z.lane_dvd m p fit v r)).symm

theorem lane_count_mul_le (v : Z.bank.Site) : Fintype.card (Z.laneRecipe key m p hp fit v).Node*p≤2*DescentNetworkSubstitution.portLoad Z.bank v :=
  DescentBatchedBank.sized_count Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen v

theorem lane_arity (v : Z.bank.Site) (t : (Z.laneProgram key m p hp fit v).Node) :
    ((Z.laneProgram key m p hp fit v).op t).arity ≤ max 2 ((2+2*h*C)*Z.width) :=
  DescentBatchedBank.sized_arity Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen v t

theorem lane_stride (v : Z.bank.Site) (t : (Z.laneProgram key m p hp fit v).Node) (j : Fin ((Z.laneProgram key m p hp fit v).op t).arity) :
    (((Z.laneProgram key m p hp fit v).op t).arg j).stride≤ max 1 (max Z.width (C*Z.width)) :=
  DescentBatchedBank.sized_stride Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen v t j

theorem lane_valid (menu : ∀π,Configures F Z.graph.arcs C Z.width π) :
    ReadsBits Z.bank (DescentLaneGates.scalar Z.graph.arcs C Z.width p (rom Z.graph.arcs C Z.width (fixedTable menu)))
      (Z.laneRecipe key m p hp fit) (Z.orderedBank key) :=
  DescentBatchedBank.sized_read Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen menu

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
