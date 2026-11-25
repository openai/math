import OAI.Hierarchy.DescentResetLaneIssue
import OAI.Hierarchy.DescentPackedResetRotorRoles

namespace OAI
/-! # A tap's true raw role from the presence of its original selected arm -/
namespace Hierarchy.DescentResetTapEmission
open DescentLaneGates DescentBatchedRotor DescentResetGates DescentPhysicalSplit DescentKernelHistory
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open DescentRotor DescentRouterSlots DescentOrderedReset DescentPackedResetRotorRoles Computability.BorderVNP.Crossing
open private DescentResetGates.rotorPortWidth from OAI.Hierarchy.DescentOrderedRotorTapRefs
open scoped Classical BigOperators Fin.CommRing
noncomputable section

theorem zero_word_digit {w : ℕ} (j : Fin w) : (bitWord w).symm 0 j=false:=by
  have zero : bitWord w (fun _=>false)=0:=by
    apply Fin.ext
    change (finFunctionFinEquiv (fun _ : Fin w=>finTwoEquiv.symm false)).val=0
    change (finFunctionFinEquiv (fun _ : Fin w=>(0:Fin 2))).val=0
    simp
  rw [←zero,Equiv.symm_apply_apply]

def onlyZero {A : Type} {size : A→ℕ} {p : ℕ} : LaneSource p size→Prop
  | .fixed b=>b=false
  | .wire _=>True

theorem focus_zero {A E Q R V : Type} {p w : ℕ} {size : A→ℕ} (addr : E→Q×Fin w)
    (slot : Q→R×V) (origin : E→V) (align : ∀e,(slot (addr e).1).2=origin e)
    (r : R) (v : V) (j : Fin w) (f : {e : E // origin e=v}→Lane p size) :
    onlyZero (focusLane f (Ordered.focus addr slot origin align r v j)):=by
  unfold Ordered.focus
  split
  · split <;> trivial
  · exact zero_word_digit j

theorem compare_tag {A : Type} {width : A→ℕ} {n p : ℕ} (left : Lane p width)
    (right : LaneSource p width) (zero : onlyZero right) :
    role ((equalOp (Y:=2^n) (.wire left) right).tag)=
      (if (equalOp (Y:=2^n) (.wire left) right).arity=2 then 5 else 3):=by
  cases right with
  | fixed b=>change b=false at zero;subst b;rfl
  | wire l=>rfl

private theorem onlyZero_transport {X : Type} {Q : X → Type} {p : ℕ}
    (width : (x : X) → Q x → ℕ) {x y : X} (eqn : x = y)
    (lane : LaneSource p (width x)) (zero : onlyZero lane) :
    onlyZero (Eq.ndrec (motive := fun t => LaneSource p (width t)) lane eqn) := by
  cases eqn
  exact zero

private abbrev roleTest {A : Type} {width : A → ℕ} {n p : ℕ}
    (op : DescentLaneGates.Op (2^n) p width) : Prop :=
  role (n:=n) op.tag = if op.arity = 2 then 5 else 3

variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable (D m p : ℕ) (hp : 0<p) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {n h b C₀ num : ℕ}
    (G : Graph n h) {hw : 0<b} {pay : ℝ} (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
local notation "u" => m*p
local notation "src" => (fun e : Item contact owner s w => first (root contact input site owner s w align e))
local notation "dst" => (fun e : Item contact owner s w => last (link contact owner s w e))
variable (P : BaseCircuit K G C₀ b (m*p) hw
    (fun e : Item contact owner s w => first (root contact input site owner s w align e))
    (fun e : Item contact owner s w => last (link contact owner s w e)) pay) (key : I↪Fin num)
local notation "H" => Physical.host G.arcs D P.layers C₀ b u
local notation "sz" => tapBits (E:=Item contact owner s w) (K:=K) D u G P
local notation "prg" => DescentBatchedRotor.program (K:=K) D m p hp contact input site owner align s w G first last P key
local notation "tapAt" => tapLane D m p hp contact input site owner align s w G first last P

local notation "widthAt" => DescentResetGates.rotorPortWidth H
  (DescentGoodRouter.position D u contact input site owner s w first last)
  (DescentNetworkSubstitution.slotWidth (DescentRouterBank.network D contact input site owner (fun _ : I => u)) (s,w))
local notation "ord" => Ordered.orderedAddress (itemKey key contact owner s w) src dst hw
local notation "fetch" => legLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl hp

set_option maxHeartbeats 2500000 in
omit [Fintype R] in
theorem tap_padding (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v))
    (r : Fin P.layers) (k : Fin m) (j : Fin (sz v i)) :
    onlyZero (p:=p) (size:=widthAt ⟨v,.inr i⟩)
      (tapLegLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl hp v i r k j):=by
  have leg (e : Leg H) (j : Fin (legBits (E:=Item contact owner s w) (K:=K) D u G P e)) :
      onlyZero (p:=p) (size:=widthAt (tap H e)) (fetch e r k j) := by
    rcases e with ⟨a,(_|_)⟩|⟨arc,(_|_)⟩
    · exact focus_zero ord (fun z=>(P.choose z,z.1)) src (fun _=>rfl) r a j
        (fun e => falseLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl a k e hp)
    · exact focus_zero ord (fun z=>(P.choose z,z.2.1)) dst (fun _=>rfl) r a j
        (fun e => trueLane D u contact input site owner align s w G first last P key (m:=m) (p:=p) rfl a k e hp)
    · trivial
    · trivial
  exact onlyZero_transport (p:=p) widthAt (tap_named H v i)
    (fetch (name H v i) r k j) (leg (name H v i) j)

set_option maxHeartbeats 2500000 in
omit [Fintype R] in
/-- Widths of underlying p-block slices do not enter this equation: the two operands
are the actual local tap lanes, before the later address-cover flattening. -/
theorem tap_role (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v))
    (z : (prg ⟨v,.inr i⟩).Node) :
    roleTest (n:=n) (p:=p) (width:=widthAt ⟨v,.inr i⟩) ((prg ⟨v,.inr i⟩).op z) := by
  rcases z with core|arm
  · rfl
  · rw [DescentResetLaneIssue.tap_select_operand D m p hp contact input site owner align s w G first last P key v i arm]
    exact compare_tag (n:=n) (p:=p) (tapAt v i true ⟨i,arm⟩) _
      (tap_padding D m p hp contact input site owner align s w G first last P key v i arm.1 arm.2.1 arm.2.2)

end
end Hierarchy.DescentResetTapEmission

end OAI
