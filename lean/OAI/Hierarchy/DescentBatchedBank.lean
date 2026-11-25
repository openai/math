import OAI.Hierarchy.DescentBatchedRotor
import OAI.Hierarchy.DescentTreeLaneProgram
import OAI.Hierarchy.DescentOrderedMixedRouter

namespace OAI
/-! # A p-column program on the actually installed ordered bank, counted by physical lanes -/

namespace Hierarchy.DescentBatchedBank
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentMixedRouter DescentRotor DescentLaneGates
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section
open private DescentNetworkSubstitution.sourceTap_at DescentNetworkSubstitution.targetTap_at DescentNetworkSubstitution.pinTap_at DescentNetworkSubstitution.read_local from OAI.Hierarchy.DescentNetworkSubstitution

section Ports
variable {D d : ℕ} {E : Type} {width : E→ℕ} (N : Network D E width)
    (M : ∀v,Network d (DescentNetworkSubstitution.Slot N v) (DescentNetworkSubstitution.slotWidth N v))
local notation "Q" => DescentNetworkSubstitution.network N M

def physicalPort (v : N.Site) (j : (M v).Site) : Boundary (M v) j→Boundary Q ⟨v,j⟩
  | .inl e=>.inl ⟨.inr ⟨v,e.val⟩,e.property.imp (congrArg (Sigma.mk v)) (congrArg (Sigma.mk v))⟩
  | .inr ⟨.inl e,h⟩=>.inl ⟨.inl e.val,Or.inl ((DescentNetworkSubstitution.sourceTap_at N M e).trans (congrArg (Sigma.mk v) h))⟩
  | .inr ⟨.inr (.inl e),h⟩=>.inl ⟨.inl e.val,Or.inr ((DescentNetworkSubstitution.targetTap_at N M e).trans (congrArg (Sigma.mk v) h))⟩
  | .inr ⟨.inr (.inr p),h⟩=>.inr ⟨p.val,(DescentNetworkSubstitution.pinTap_at N M p).trans (congrArg (Sigma.mk v) h)⟩

def portMap (v : N.Site) (j : (M v).Site) : PortMap (boundaryWidth (M v) j) (boundaryWidth Q ⟨v,j⟩) where
  slot:=physicalPort N M v j
  sameWidth s:=by rcases s with e|⟨e|(e|p),h⟩ <;> rfl

theorem portBit (v : N.Site) (j : (M v).Site) (k : BitRef (boundaryWidth (M v) j)) :
    (portMap N M v j).bit k=substituteBit N M v j k := by rcases k with ⟨e|⟨e|(e|p),h⟩,i⟩ <;> rfl
private theorem substituted_load [Fintype E] (v : N.Site) (j : (M v).Site)
    (finiteSlots : Fintype (DescentNetworkSubstitution.Slot N v)) :
    DescentNetworkSubstitution.portLoad Q ⟨v,j⟩ =
      @DescentNetworkSubstitution.portLoad d _ _ finiteSlots (M v) j := by
  exact (DescentNetworkSubstitution.portLoad_substitute N M v j).trans
    (congrArg (fun fs : Fintype (DescentNetworkSubstitution.Slot N v) =>
      @DescentNetworkSubstitution.portLoad d _ _ fs (M v) j) (Subsingleton.elim _ finiteSlots))
end Ports

variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits M : ℕ} (G : Graph n h) (hw : 0<bits) (m p : ℕ) (hp : 0<p)
variable (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (key : I↪Fin M) (D : ℕ) {s : Bool} {w : W}
local notation "wt" => (fun _ : I=>m*p)
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw (m*p) contact input site owner align
local notation "A" => device (K:=K) (C₀:=C₀) G hw (m*p) contact input site owner align (D:=D)
local notation "T" => DescentMixedRouter.Ordered.localTables (K:=K) (C₀:=C₀) G hw (m*p) contact input site owner align key D
local notation "lens" => DescentNetworkSubstitution.slotWidth B (s,w)

def deviceProgram : (z : Ch s w)→(v : (A z).Site)→DescentLaneGates.Program (2^n) p (boundaryWidth (A z) v)
  | .exceptional t=>DescentTreeLaneProgram.program D contact input site owner align m p hp s w t.book.codes key (2^n)
  | .good first last _ P=>DescentBatchedRotor.program D m p hp contact input site owner align s w G first last P key

local notation "localAt" => deviceProgram G hw m p hp contact input site owner align key D
variable (menu : ∀π,Configures K G.arcs C₀ bits π)
local notation "romWord" => rom G.arcs C₀ bits (fixedTable menu)
local notation "evalAt" => DescentLaneGates.scalar G.arcs C₀ bits p romWord

omit [Fintype R] in
theorem local_read (z : Ch s w) (v : (A z).Site) (a : (A z).Assignment) (x : Ports lens) :
    (localAt z v).recipe.value evalAt (assignmentBit (A z) a x v)=(A z).read (T z) a x v := by
  cases z with
  | exceptional t=>exact DescentTreeLaneProgram.program_read D contact input site owner align m p hp s w t.book.codes key G.arcs C₀ bits romWord a x v
  | good first last pay P=>exact DescentBatchedRotor.program_read D m p hp contact input site owner align s w G first last P key menu a x v

variable (select : ∀s w,Choice (K:=K) (C₀:=C₀) G hw (m*p) contact input site owner align s w)
local notation "bank" => DescentMixedRouter.network (K:=K) (C₀:=C₀) G hw (m*p) contact input site owner align select D
local notation "coeff" => DescentMixedRouter.Ordered.coefficients (K:=K) (C₀:=C₀) G hw (m*p) contact input site owner align key D select
local notation "devices" => fun t : (B).Site=>A (select (Prod.fst t) (Prod.snd t))

def program (v : (bank).Site) : DescentLaneGates.Program (2^n) p (boundaryWidth bank v) :=
  (localAt (select v.1.1 v.1.2) v.2).transport (portMap B devices v.1 v.2)

local notation "atSite" => program G hw m p hp contact input site owner align key D select

private theorem local_node_count :
    (z : Ch s w) → (j : (A z).Site) →
      Fintype.card (localAt z j).Node * p ≤ 2 * DescentNetworkSubstitution.portLoad (A z) j
  | .exceptional t, j =>
    ((Nat.le_div_iff_mul_le hp).mp (DescentTreeLaneProgram.node_count_bound
      D contact input site owner align m p hp s w t.book.codes key (2^n) j)).trans
        (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
  | .good first last _ P, j =>
    DescentBatchedRotor.node_count_mul_le D m p hp contact input site owner align s w G first last P key j

private theorem local_load (pair : Bool × W) (j : (A (select pair.1 pair.2)).Site) :
    DescentNetworkSubstitution.portLoad bank ⟨pair,j⟩ =
      DescentNetworkSubstitution.portLoad (A (select pair.1 pair.2)) j := by
  obtain ⟨s,w⟩ := pair
  exact substituted_load B devices (s,w) j inferInstance

theorem node_count_mul_le (v : (bank).Site) : Fintype.card (atSite v).Node*p≤2*DescentNetworkSubstitution.portLoad bank v := by
  rcases v with ⟨⟨s,w⟩,j⟩
  have card : Fintype.card (atSite ⟨(s,w),j⟩).Node =
      Fintype.card (localAt (select s w) j).Node := Fintype.card_congr (Equiv.refl _)
  exact (congrArg (· * p) card).le.trans
    ((local_node_count G hw m p hp contact input site owner align key D (select s w) j).trans_eq
      (congrArg (2 * ·) (local_load G hw m p contact input site owner align D select (s,w) j).symm))

omit [Fintype R] in
theorem arity_bound (v : (bank).Site) (t : (atSite v).Node) : ((atSite v).op t).arity≤ max 2 ((2+2*h*C₀)*bits) := by
  have bound {s w} (z : Ch s w) (j : (A z).Site) (t : (localAt z j).Node) : ((localAt z j).op t).arity≤ max 2 ((2+2*h*C₀)*bits) := by
    cases z with
    | exceptional d=>exact (DescentTreeLaneProgram.node_arity D contact input site owner align m p hp s w d.book.codes key (2^n) j t).le.trans (Nat.le_max_left _ _)
    | good first last pay P=>exact DescentBatchedRotor.arity_bound D m p hp contact input site owner align s w G first last P key j t
  exact bound _ _ t

omit [Fintype R] in
theorem stride_bound (v : (bank).Site) (t : (atSite v).Node) (j : Fin ((atSite v).op t).arity) :
    (((atSite v).op t).arg j).stride≤ max 1 (max bits (C₀*bits)) := by
  have bound {s w} (z : Ch s w) (k : (A z).Site) (t : (localAt z k).Node) (j : Fin ((localAt z k).op t).arity) :
      (((localAt z k).op t).arg j).stride≤ max 1 (max bits (C₀*bits)) := by
    cases z with
    | exceptional d=>exact (DescentTreeLaneProgram.stride_one D contact input site owner align m p hp s w d.book.codes key (2^n) k t j).le.trans (Nat.le_max_left _ _)
    | good first last pay P=>exact DescentBatchedRotor.stride_bound D m p hp contact input site owner align s w G first last P key k t j
  exact bound _ _ t j

theorem control_count (v : (bank).Site) : (∑t : (atSite v).Node,(1+((atSite v).op t).arity))*p≤
    (2*DescentNetworkSubstitution.portLoad bank v)*(1+max 2 ((2+2*h*C₀)*bits)) := by
  let rate:=1+max 2 ((2+2*h*C₀)*bits)
  have each : (∑t : (atSite v).Node, (1 + ((atSite v).op t).arity))≤Fintype.card (atSite v).Node*rate := by
    calc
      _ ≤ ∑_ : (atSite v).Node, rate := by
        apply Finset.sum_le_sum
        intro t _
        exact Nat.add_le_add_left (arity_bound G hw m p hp contact input site owner align key D select v t) 1
      _ = Fintype.card (atSite v).Node * rate := by simp
  calc
    _ ≤ Fintype.card (atSite v).Node*rate*p:=Nat.mul_le_mul_right p each
    _ = Fintype.card (atSite v).Node*p*rate:=by ring
    _ ≤ _:=Nat.mul_le_mul_right rate (node_count_mul_le G hw m p hp contact input site owner align key D select v)

set_option maxHeartbeats 1200000 in
omit [Fintype R] in
theorem program_read (a : (bank).Assignment) (x : Ports (DescentRouterBank.publicWidth input wt))
    (v : (bank).Site) :
    (atSite v).recipe.value evalAt (assignmentBit bank a x v) = (bank).read coeff a x v := by
  obtain ⟨⟨s,w⟩,j⟩ := v
  let z := DescentNetworkSubstitution.assignmentEquiv B devices a
  let y := DescentNetworkSubstitution.visible B z.1 x (s,w)
  let prog := localAt (select s w) j
  let f := portMap B devices (s,w) j
  let globalRead := assignmentBit bank a x ⟨(s,w),j⟩
  have reads : globalRead ∘ f.bit = assignmentBit (A (select s w)) (z.2 (s,w)) y j := by
    funext t
    exact (congrArg globalRead (portBit B devices (s,w) j t)).trans
      (substituteBit_read B devices a x (s,w) j t)
  have mounted : (prog.transport f).recipe.value evalAt globalRead =
      (prog.recipe.reroute f.bit).value evalAt globalRead :=
    congrArg (fun r : BitRecipe (CanonicalTag (2^n)) (Boundary bank ⟨(s,w),j⟩)
      (boundaryWidth bank ⟨(s,w),j⟩) => r.value evalAt globalRead)
      (DescentLaneGates.Program.transport_recipe prog f)
  exact mounted.trans ((BitRecipe.reroute_eval prog.recipe evalAt f.bit globalRead).trans
    ((congrArg (prog.recipe.value evalAt) reads).trans
      ((local_read G hw m p hp contact input site owner align key D menu (select s w) j (z.2 (s,w)) y).trans
        (DescentNetworkSubstitution.read_local B devices
          (fun t : Bool × W => T (select (Prod.fst t) (Prod.snd t))) a x (s,w) j).symm)))

omit [Fintype R] in
theorem recipe_local (v : (bank).Site) (read : ∀e:Incident bank v,Word ((bank).width e.val))
    (pins : ∀q:Attached bank v,Word (DescentRouterBank.publicWidth input wt q.val)) :
    (atSite v).recipe.value evalAt (siteBit read pins)=coeff v read pins := by
  let a:=Calls.localWire (N:=bank) v read
  let x:=Calls.localPin (N:=bank) v pins
  have inputs : siteBit read pins=assignmentBit bank a x v := by
    funext t
    rcases t with ⟨e|q,j⟩
    · simp [siteBit,assignmentBit,a,Calls.localWire,e.property]
    · simp [siteBit,assignmentBit,x,Calls.localPin,q.property]
  rw [inputs,program_read]
  unfold Network.read
  congr 1 <;> funext e <;> simp [a,x,Calls.localWire,Calls.localPin,e.property]

end
end Hierarchy.DescentBatchedBank

end OAI
