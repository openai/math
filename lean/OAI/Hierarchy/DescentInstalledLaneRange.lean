import OAI.Hierarchy.DescentEqualityRangeDigits
import OAI.Hierarchy.DescentBundleBank

namespace OAI
/-! # Operand range digits survive installation at the actual physical ports -/
set_option quotPrecheck false

namespace Hierarchy.DescentRetainedRangeDigits
open DescentBundleHistory DescentLaneGates
noncomputable section
variable {A B : Type} {w : A→ℕ} {v : B→ℕ} {p Y : ℕ}

theorem before_multiple (f : PortMap w v) (after : ∀i,v i=v i/p*p) (i : A) :
    w i=w i/p*p :=by simpa only [f.sameWidth i] using after (f.slot i)

theorem transported_code (f : PortMap w v) (l : Lane p w) :
    laneCode (fun j=>v j/p) (l.transport f)=laneCode (fun j=>w j/p) l :=by
  unfold laneCode
  simp only [Lane.transport,Lane.residue,Lane.count,Lane.bundleStart,f.sameWidth]

theorem mounted_slot (f : PortMap w v) (P : Program Y p w) (u : P.Node)
    (after : ∀i,v i=v i/p*p) (positive : 0<p) (slot : ℕ) (field : Fin 3) :
    atSlot (ofProgram (fun j=>v j/p) after positive (P.transport f)) u slot field=
    atSlot (ofProgram (fun j=>w j/p) (before_multiple f after) positive P) u slot field :=by
  have codes : operandCodes (fun j=>v j/p) ((P.transport f).op u)=
      operandCodes (fun j=>w j/p) (P.op u) := by
    change List.ofFn (fun j : Fin (P.op u).arity =>
        [laneCode (fun i=>v i/p) (((P.op u).arg j).transport f)]) =
      List.ofFn (fun j : Fin (P.op u).arity => [laneCode (fun i=>w i/p) ((P.op u).arg j)])
    exact congrArg List.ofFn (funext fun j =>
      congrArg (fun code=>[code]) (transported_code f ((P.op u).arg j)))
  exact of_fields (ofProgram (fun j=>v j/p) after positive (P.transport f)) u
    (ofProgram (fun j=>w j/p) (before_multiple f after) positive P) u
    ((lane_codes _ after positive (P.transport f) u).trans
      (codes.trans (lane_codes _ (before_multiple f after) positive P u).symm)) slot field

end
end Hierarchy.DescentRetainedRangeDigits

namespace Hierarchy.DescentBatchedBank
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentMixedRouter DescentRotor DescentLaneGates
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section
open DescentBundleHistory DescentRetainedRangeDigits
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits M : ℕ} (G : Graph n h) (hw : 0<bits) (m p : ℕ) (hp : 0<p)
variable (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (key : I↪Fin M) (D : ℕ) {s : Bool} {w : W}
local notation "rack" => DescentRouterBank.network D contact input site owner (fun _ : I=>m*p)
variable (select : ∀s w,Choice (K:=K) (C₀:=C₀) G hw (m*p) contact input site owner align s w)
local notation "bank" => DescentMixedRouter.network (K:=K) (C₀:=C₀) G hw (m*p) contact input site owner align select D
local notation "devices" => fun a : (rack).Site =>
  device (K:=K) (C₀:=C₀) G hw (m*p) contact input site owner align (D:=D) (select a.1 a.2)

omit [Fintype R] in
theorem installed_range (v : (bank).Site)
    (mul : ∀i,boundaryWidth bank v i=boundaryWidth bank v i/p*p) :
    let op : DescentLaneGates.Program (2^n) p (boundaryWidth (devices v.1) v.2) :=
      deviceProgram (s:=v.1.1) (w:=v.1.2) G hw m p hp contact input site owner align key D
        (select v.1.1 v.1.2) v.2
    let ports : PortMap (boundaryWidth (devices v.1) v.2) (boundaryWidth bank v) :=
      portMap rack devices v.1 v.2
    ∀ (t : op.Node) (arg : ℕ) (f : Fin 3),
      atSlot (ofProgram (fun j=>boundaryWidth bank v j/p) mul hp (op.transport ports)) t arg f =
        atSlot (ofProgram (fun j=>boundaryWidth (devices v.1) v.2 j/p)
          (before_multiple ports mul) hp op) t arg f := by
  intro op ports t arg f
  exact mounted_slot ports op t mul hp arg f

end
end Hierarchy.DescentBatchedBank

namespace Hierarchy.DescentBatchedBank
open DescentBundleHistory DescentRetainedRangeDigits DescentLaneGates
open Computability.BorderVNP.Crossing DescentRotor DescentKernelHistory DescentResetGates DescentMixedRouter
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits M : ℕ} (G : Graph n h) (hw : 0<bits) (u m p : ℕ) (hp : 0<p) (fit : u=m*p)
variable (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (key : I↪Fin M) (D : ℕ)
variable (select : ∀s w,Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align s w)
local notation "bank" => DescentMixedRouter.network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D
local notation "rack" => DescentRouterBank.network D contact input site owner (fun _ : I=>u)
local notation "devices" => fun a : (rack).Site=>device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) (select a.1 a.2)
local notation "pAt" => sizedProgram (K:=K) (C₀:=C₀) G hw u m p hp fit contact input site owner align key D select

include fit hp key in
/-- The original local menu with the same unit equation as the installed program. -/
def sizedLocal (v : (bank).Site) : DescentLaneGates.Program (2^n) p (boundaryWidth (devices v.1) v.2) :=by
  subst u
  exact deviceProgram G hw m p hp contact input site owner align key D (select v.1.1 v.1.2) v.2

local notation "old" => sizedLocal G hw u m p hp fit contact input site owner align key D select

def sizedLocalNode (v : (bank).Site) : (pAt v).Node ≃ (old v).Node :=by
  subst u
  exact Equiv.refl _

omit [Fintype R] in
theorem sized_range (v : (bank).Site) (mul : ∀i,boundaryWidth bank v i=boundaryWidth bank v i/p*p)
    (t : (pAt v).Node) (arg : ℕ) (f : Fin 3) :
    atSlot (r:=(pAt v).recipe) (ofProgram (fun j=>boundaryWidth bank v j/p) mul hp (pAt v)) t arg f=
      atSlot (r:=(old v).recipe) (ofProgram (fun j=>boundaryWidth (devices v.1) v.2 j/p)
        (before_multiple (portMap rack devices v.1 v.2) mul) hp (old v))
          (sizedLocalNode G hw u m p hp fit contact input site owner align key D select v t) arg f :=by
  subst u
  exact installed_range G hw m p hp contact input site owner align key D select v mul t arg f

end
end Hierarchy.DescentBatchedBank

namespace Hierarchy.DescentSixParty.ResetInput
open DescentBundleHistory DescentRetainedRangeDigits DescentBatchedBank
open Computability.BorderVNP.Crossing DescentRotor DescentChosenRouter DescentKernelHistory DescentResetGates
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht L : ℕ} (Z : ResetInput A price ε h C Ht) (key : A.graph.Edge↪Fin L)
variable (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
local notation "R" => Z.placement
local notation "chosen" => DescentChosenRouter.selected R Z.graph Z.positive Z.pay Z.circuit

local notation "rack" => DescentRouterBank.network d (R).contact (R).input (R).site (R).owner (fun _ : A.graph.Edge=>Z.unit)
local notation "devices" => fun u : (rack).Site=>DescentMixedRouter.device Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align (D:=d) (chosen u.1 u.2)
local notation "localProgram" => sizedLocal Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen
local notation "nodes" => sizedLocalNode Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen

theorem laneShape_range (v : Z.bank.Site) (t : (Z.laneRecipe key m p hp fit v).Node) (arg : ℕ) (f : Fin 3) :
    atSlot (r:=Z.laneRecipe key m p hp fit v) (Z.laneShape key m p hp fit v) t arg f=
      atSlot (r:=(localProgram v).recipe) (ofProgram (fun a=>boundaryWidth (devices v.1) v.2 a/p)
        (before_multiple (portMap rack devices v.1 v.2) (Z.laneWidth_eq m p fit v))
        hp (localProgram v)) (nodes v t) arg f :=
  sized_range Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen v
    (Z.laneWidth_eq m p fit v) t arg f

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
