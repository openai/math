import OAI.Hierarchy.DescentResetTapArity
import OAI.Hierarchy.DescentPrimitiveBirthCases

namespace OAI
/-! # The primitive word at a physical reset tap or exceptional tree cell -/
namespace Hierarchy.DescentResetTapEmission
open DescentLaneGates DescentBatchedRotor DescentResetGates DescentPhysicalSplit DescentKernelHistory
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open DescentRotor DescentRouterSlots DescentOrderedReset DescentPackedResetRotorRoles Computability.BorderVNP.Crossing
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable (D m p : ℕ) (hp : 0<p) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {n h b C₀ num : ℕ}
    (G : Graph n h) {hw : 0<b} {pay : ℝ} (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
local notation "u" => m*p
variable (P : BaseCircuit K G C₀ b (m*p) hw
    (fun e : Item contact owner s w => first (root contact input site owner s w align e))
    (fun e : Item contact owner s w => last (link contact owner s w e)) pay) (key : I↪Fin num)
local notation "H" => Physical.host G.arcs D P.layers C₀ b u
local notation "sz" => tapBits D u G P
local notation "prg" => DescentBatchedRotor.program (K:=K) D m p hp contact input site owner align s w G first last P key
local notation "tapAt" => tapLane D m p hp contact input site owner align s w G first last P

local notation "A" => DescentGoodRouter.device D u contact input site owner align s w G first last P
variable (Z : DescentPrimitiveBirth.Layout) (slot : Fin Z.nodes) (cls : DescentSIMDLookup.Cell Z.classBits)
  (paid : DescentSIMDLookup.Cell Z.paidBits) (spans : Fin Z.arguments→DescentSIMDLookup.Cell Z.spanBits)
  (roots : Fin Z.roots→DescentSIMDLookup.Cell Z.rootBits)
open DescentResetMetadataInputs

omit [Fintype R] in
/-- This uses the permanent flattened F6 words to distinguish the one-wire tap from the two-wire tap. -/
theorem native_tap_role (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v)) (a : (prg ⟨v,.inr i⟩).Node)
    (units : Boundary A ⟨v,.inr i⟩→ℕ)
    (multiple : ∀j,boundaryWidth A ⟨v,.inr i⟩ j=units j*p)
    (enough : ((DescentBundleHistory.ofProgram units multiple hp (prg ⟨v,.inr i⟩)).recipe hp).arity a≤Z.arguments)
    (spanValues : ∀j,(spans j).val=argumentSpan (DescentBundleHistory.ofProgram units multiple hp (prg ⟨v,.inr i⟩)) a j.val)
    (live : slot.val<paid.val) (position : cls.val=4) :
    Z.raw slot cls paid spans roots=(role ((prg ⟨v,.inr i⟩).op a).tag : DescentSIMDLookup.Cell Z.rootBits):=by
  have truth:=Z.tap_arity slot cls paid spans roots units multiple hp (prg ⟨v,.inr i⟩) a
    (real_tap_arity D m p hp contact input site owner align s w G first last P key v i a) enough spanValues live position
  have roleEq := tap_role D m p hp contact input site owner align s w G first last P key v i a
  change role ((prg ⟨v,.inr i⟩).op a).tag = (if ((prg ⟨v,.inr i⟩).op a).arity=2 then 5 else 3) at roleEq
  rw [truth,roleEq]
  split <;> rfl

end
end Hierarchy.DescentResetTapEmission
namespace Hierarchy.DescentTreeLaneProgram
open Computability.BorderVNP.Crossing DescentKernelHistory DescentRouterSlots DescentContactTree DescentResetGates
open DescentOrderedReset DescentOrderedWords DescentTreeGateRefs
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [CommSemiring K]
variable (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (m p : ℕ) (hp : 0<p)
variable (s : Bool) (w : W) {depth n : ℕ} (book : LinkId owner s w ↪ Node depth) (key : I↪Fin n)
local notation "wt" => fun _ : I=>m*p
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "lp" => link contact owner s w
local notation "cost" => amount contact owner wt s w
local notation "N" => DescentFixedExceptionalRouter.device D contact input site owner wt s w book
variable (Z : DescentPrimitiveBirth.Layout) (slot : Fin Z.nodes) (cls : DescentSIMDLookup.Cell Z.classBits)
  (paid : DescentSIMDLookup.Cell Z.paidBits) (spans : Fin Z.arguments→DescentSIMDLookup.Cell Z.spanBits)
  (roots : Fin Z.roots→DescentSIMDLookup.Cell Z.rootBits)
omit [Fintype R] in
theorem native_tree_role {n : ℕ} (q : Physical.Site depth)
    (a : (program D contact input site owner align m p hp s w book key (2^n) q).Node)
    (live : slot.val<paid.val) (position : cls.val=5) :
    Z.raw slot cls paid spans roots=(DescentPackedResetRotorRoles.role
      (((program D contact input site owner align m p hp s w book key (2^n) q).op a).tag) : DescentSIMDLookup.Cell Z.rootBits):=by
  exact Z.fallback slot cls paid spans roots live position

end
end Hierarchy.DescentTreeLaneProgram

end OAI
