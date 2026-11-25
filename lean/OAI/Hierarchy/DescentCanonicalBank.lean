import OAI.Hierarchy.DescentCanonicalRotor
import OAI.Hierarchy.DescentTreeGateRefs
import OAI.Hierarchy.DescentTreeCellLoad
import OAI.Hierarchy.DescentOrderedMixedRouter

namespace OAI
/-! # Fixed-alphabet bit recipes for every actual ordered reset-bank coefficient -/

namespace Hierarchy.DescentCanonicalBank
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentMixedRouter DescentRotor
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section
open private DescentNetworkSubstitution.read_local from OAI.Hierarchy.DescentNetworkSubstitution
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits M : ℕ} (G : Graph n h) (hw : 0<bits) (u : ℕ) (contact : I→C) (input : Bool→I→R)
variable (site : Bool→R→W) (owner : Bool→C→W) (align : ∀s i,site s (input s i)=owner s (contact i)) (key : I↪Fin M)
variable (D : ℕ) {s : Bool} {w : W}
local notation "wt" => (fun _ : I=>u)
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align
local notation "A" => device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D)
local notation "T" => DescentMixedRouter.Ordered.localTables (K:=K) (C₀:=C₀) G hw u contact input site owner align key D
local notation "lens" => DescentNetworkSubstitution.slotWidth B (s,w)

def localProgram : (z : Ch s w)→(v : (A z).Site)→Program (2^n) (boundaryWidth (A z) v)
  | .exceptional t=>DescentTreeGateRefs.program D contact input site owner wt align s w t.book.codes key (2^n)
  | .good first last _ P=>DescentCanonicalRotor.program D u contact input site owner align s w G first last P key

variable (menu : ∀π,Configures K G.arcs C₀ bits π)
local notation "romWord" => rom G.arcs C₀ bits (fixedTable menu)
local notation "scalar" => canonicalScalar G.arcs C₀ bits romWord
local notation "localAt" => localProgram G hw u contact input site owner align key D

omit [Fintype R] in
theorem local_read (z : Ch s w) (v : (A z).Site) (a : (A z).Assignment) (p : Ports lens) :
    (localAt z v).recipe.value scalar (assignmentBit (A z) a p v)=(A z).read (T z) a p v := by
  cases z with
  | exceptional t=>exact DescentTreeGateRefs.program_read D contact input site owner wt align s w t.book.codes key G.arcs C₀ bits romWord a p v
  | good first last pay P=>exact DescentCanonicalRotor.program_read D u contact input site owner align s w G first last P key menu a p v

variable (select : ∀ s w, Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align s w)
local notation "bank" => DescentMixedRouter.network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D
local notation "coeff" => DescentMixedRouter.Ordered.coefficients (K:=K) (C₀:=C₀) G hw u contact input site owner align key D select
local notation "devices" => fun t : (B).Site => A (select (Prod.fst t) (Prod.snd t))

/-- One immutable tag alphabet works for every host, colony, epoch, tree selector and packet row. -/
def recipe (v : (bank).Site) : BitRecipe (CanonicalTag (2^n)) (Boundary bank v) (boundaryWidth bank v) :=
  (localAt (select v.1.1 v.1.2) v.2).recipe.reroute (substituteBit B devices v.1 v.2)

local notation "atSite" => recipe G hw u contact input site owner align key D select

omit [Fintype R] in
theorem nodeBits_bound (v : (bank).Site) (i : (atSite v).Node) :
    (atSite v).nodeBits i≤ max 2 ((2+2*h*C₀)*bits) := by
  have bound {s w} (z : Ch s w) (j : (A z).Site) (t : (localAt z j).Node) : ((localAt z j).op t).bitCount≤ max 2 ((2+2*h*C₀)*bits) := by
    cases z with
    | exceptional d=>exact (DescentTreeGateRefs.node_bits D contact input site owner wt align s w d.book.codes key (2^n) j t).le.trans (Nat.le_max_left _ _)
    | good first last pay P=>exact DescentCanonicalRotor.node_bits D u contact input site owner align s w G first last P key j t
  exact bound _ _ i

omit [Fintype R] in
theorem arity_bound (v : (bank).Site) (i : (atSite v).Node) : (atSite v).arity i≤2*h+2 := by
  have bound {s w} (z : Ch s w) (j : (A z).Site) (t : (localAt z j).Node) : ((localAt z j).op t).arity≤2*h+2 := by
    cases z with
    | exceptional d=>rw [show ((localAt (.exceptional d) j).op t).arity=2 from DescentTreeGateRefs.node_arity D contact input site owner wt align s w d.book.codes key (2^n) j t];omega
    | good first last pay P=>exact DescentCanonicalRotor.node_arity D u contact input site owner align s w G first last P key j t
  exact bound _ _ i

private theorem local_node_count_bound :
    (z : Ch s w) → (j : (A z).Site) →
      Fintype.card (localAt z j).Node ≤ 2 * DescentNetworkSubstitution.portLoad (A z) j
  | .exceptional d, j =>
    (DescentTreeGateRefs.node_count D contact input site owner wt align s w d.book.codes key (2^n) j).le.trans
      ((DescentFixedExceptionalRouter.nodeWidth_le_portLoad D contact input site owner wt align s w d.book.codes j).trans
        (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)))
  | .good first last _ P, j =>
    DescentCanonicalRotor.node_count_le D u contact input site owner align s w G first last P key j

omit [Fintype R] in
private theorem recipe_card (v : (bank).Site) :
    Fintype.card (atSite v).Node = Fintype.card (localAt (select v.1.1 v.1.2) v.2).Node :=
  Fintype.card_congr (Equiv.refl _)

private theorem substituted_load {P : Type} {width : P → ℕ} [Fintype P] {d : ℕ}
    (N : Network D P width) (parts : (v : N.Site) → Network d
      (DescentNetworkSubstitution.Slot N v) (DescentNetworkSubstitution.slotWidth N v))
    (v : N.Site) (j : (parts v).Site) (finiteSlots : Fintype (DescentNetworkSubstitution.Slot N v)) :
    DescentNetworkSubstitution.portLoad (DescentNetworkSubstitution.network N parts) ⟨v,j⟩ =
      @DescentNetworkSubstitution.portLoad d _ _ finiteSlots (parts v) j := by
  exact (DescentNetworkSubstitution.portLoad_substitute N parts v j).trans
    (congrArg (fun enumeration : Fintype (DescentNetworkSubstitution.Slot N v) =>
      @DescentNetworkSubstitution.portLoad d _ _ enumeration (parts v) j)
      (Subsingleton.elim _ finiteSlots))

private theorem local_load (pair : Bool × W) (j : (A (select pair.1 pair.2)).Site) :
    DescentNetworkSubstitution.portLoad bank ⟨pair,j⟩ =
      DescentNetworkSubstitution.portLoad (A (select pair.1 pair.2)) j := by
  obtain ⟨s,w⟩ := pair
  exact substituted_load D B devices (s,w) j inferInstance

/-- Per-site node births are paid by the actual surviving wire and terminal widths.
A true rotor tap pays both its entire unchanged spine word and its selected leg. -/
theorem node_count_bound (v : (bank).Site) : Fintype.card (atSite v).Node ≤ 2*DescentNetworkSubstitution.portLoad bank v := by
  rcases v with ⟨⟨s,w⟩,j⟩
  exact (recipe_card G hw u contact input site owner align key D select ⟨(s,w),j⟩).le.trans
    ((local_node_count_bound G hw u contact input site owner align key D (select s w) j).trans_eq
      (congrArg (2 * ·) (local_load G hw u contact input site owner align D select (s,w) j).symm))

/-- Serialized gate names, argument lengths, and referenced bit positions all charge the same
physical incidence at a factor depending only on the fixed rotor. -/
theorem operand_budget (v : (bank).Site) :
    (∑ i : (atSite v).Node, (1+(atSite v).arity i+(atSite v).nodeBits i)) ≤
      (2*DescentNetworkSubstitution.portLoad bank v)*(1+(2*h+2)+max 2 ((2+2*h*C₀)*bits)) := by
  let rate:=1+(2*h+2)+max 2 ((2+2*h*C₀)*bits)
  calc
    _ ≤ ∑_ : (atSite v).Node,rate := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.add_le_add (Nat.add_le_add_left (arity_bound G hw u contact input site owner align key D select v i) 1)
        (nodeBits_bound G hw u contact input site owner align key D select v i)
    _ = Fintype.card (atSite v).Node*rate := by simp
    _ ≤ _ := Nat.mul_le_mul_right rate (node_count_bound G hw u contact input site owner align key D select v)

omit [Fintype R] in
theorem recipe_read (a : (bank).Assignment) (p : Ports (DescentRouterBank.publicWidth input wt)) (v : (bank).Site) :
    (atSite v).value scalar (assignmentBit bank a p v)=(bank).read coeff a p v := by
  obtain ⟨⟨s,w⟩,j⟩:=v
  let z:=DescentNetworkSubstitution.assignmentEquiv B devices a
  let x:=DescentNetworkSubstitution.visible B z.1 p (s,w)
  have reads : assignmentBit bank a p ⟨(s,w),j⟩ ∘ substituteBit B devices (s,w) j = assignmentBit (A (select s w)) (z.2 (s,w)) x j :=
    funext (substituteBit_read B devices a p (s,w) j)
  let r := (localAt (select s w) j).recipe
  exact (BitRecipe.reroute_eval r scalar (substituteBit B devices (s,w) j)
    (assignmentBit bank a p ⟨(s,w),j⟩)).trans
    ((congrArg (r.value scalar) reads).trans
      ((local_read G hw u contact input site owner align key D menu (select s w) j (z.2 (s,w)) x).trans
        (DescentNetworkSubstitution.read_local B devices
          (fun t : Bool × W => T (select (Prod.fst t) (Prod.snd t))) a p (s,w) j).symm))

omit [Fintype R] in
/-- Actual coefficients at arbitrary local operands, ready for the stage's ordered trunk readback. -/
theorem recipe_local (v : (bank).Site) (wires : ∀e:Incident bank v,Word ((bank).width e.val))
    (pins : ∀p:Attached bank v,Word (DescentRouterBank.publicWidth input wt p.val)) :
    (atSite v).value scalar (siteBit wires pins)=coeff v wires pins := by
  let a:=Calls.localWire (N:=bank) v wires
  let x:=Calls.localPin (N:=bank) v pins
  have inputs : siteBit wires pins=assignmentBit bank a x v := by
    funext b
    rcases b with ⟨e|p,j⟩
    · simp [siteBit,assignmentBit,a,Calls.localWire,e.property]
    · simp [siteBit,assignmentBit,x,Calls.localPin,p.property]
  rw [inputs,recipe_read]
  unfold Network.read
  congr 1 <;> funext e <;> simp [a,x,Calls.localWire,Calls.localPin,e.property]

end
end Hierarchy.DescentCanonicalBank

end OAI
