import OAI.Hierarchy.DescentResetTapEmission

namespace OAI
/-! # Arity of the two physical reset tap instructions -/
namespace Hierarchy.DescentResetTapEmission
open DescentLaneGates DescentBatchedRotor DescentResetGates DescentPhysicalSplit DescentKernelHistory
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open DescentRotor DescentRouterSlots DescentOrderedReset DescentPackedResetRotorRoles Computability.BorderVNP.Crossing
open private DescentResetGates.rotorPortWidth from OAI.Hierarchy.DescentOrderedRotorTapRefs
open scoped Classical BigOperators
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
local notation "prg" => DescentBatchedRotor.program (K:=K) D m p hp contact input site owner align s w G first last P key
local notation "widthAt" => DescentResetGates.rotorPortWidth H
  (DescentGoodRouter.position D u contact input site owner s w first last)
  (DescentNetworkSubstitution.slotWidth (DescentRouterBank.network D contact input site owner (fun _ : I => u)) (s,w))

private abbrev tapArity {A : Type} {Y p : ℕ} {width : A → ℕ}
    (op : DescentLaneGates.Op Y p width) : Prop :=
  op.arity = 1 ∨ op.arity = 2

private theorem wire_arity {A : Type} {Y p : ℕ} {width : A→ℕ} (l : Lane p width) (r : LaneSource p width) :
    tapArity (DescentLaneGates.equalOp (Y:=Y) (.wire l) r) := by
  cases r with
  | fixed b => exact Or.inl rfl
  | wire t => exact Or.inr rfl

set_option maxHeartbeats 2500000 in
omit [Fintype R] in
theorem real_tap_arity (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v))
    (a : (prg ⟨v,.inr i⟩).Node) :
    tapArity (Y:=2^n) (p:=p) (width:=widthAt ⟨v,.inr i⟩) ((prg ⟨v,.inr i⟩).op a) := by
  rcases a with wire|arm
  · exact Or.inr rfl
  · rw [DescentResetLaneIssue.tap_select_operand D m p hp contact input site owner align s w G first last P key v i arm]
    exact wire_arity _ _

end
end Hierarchy.DescentResetTapEmission

end OAI
