import OAI.Hierarchy.DescentTreeGateRefs
import OAI.Hierarchy.DescentTreeCellLoad
import OAI.Hierarchy.DescentLaneGates

namespace OAI
/-! # One equality per p-bit item lane in the actual ordered exceptional tree -/

namespace Hierarchy.DescentTreeLaneProgram
open Computability.BorderVNP.Crossing DescentKernelHistory DescentRouterSlots DescentContactTree DescentResetGates
open DescentOrderedReset DescentOrderedWords DescentTreeGateRefs
open scoped Classical BigOperators
noncomputable section
variable {A : Type} {width : A→ℕ} {p : ℕ}

private def consecutive (hp : 0<p) (atRef : Fin p→BitRef width) :=
  ∀j : Fin p,(atRef j).1=(atRef ⟨0,hp⟩).1 ∧ (atRef j).2.val=(atRef ⟨0,hp⟩).2.val+j.val

/-- Store the one containing port and the starting offset of an entire unit-stride row. -/
private def segment (hp : 0<p) (atRef : Fin p→BitRef width) (good : consecutive hp atRef) :
    DescentLaneGates.Lane p width where
  port := (atRef ⟨0,hp⟩).1
  start := (atRef ⟨0,hp⟩).2.val
  stride := 1
  fits j := by rw [Nat.one_mul,←(good j).2,←(good j).1];exact (atRef j).2.isLt

private theorem segment_read (hp : 0<p) (atRef : Fin p→BitRef width) (good : consecutive hp atRef) (j : Fin p) :
    (segment hp atRef good).atBit j=atRef j := by
  refine Sigma.ext ?_ ?_
  · exact (good j).1.symm
  apply (Fin.heq_ext_iff (congrArg width (good j).1.symm)).mpr
  change (atRef ⟨0,hp⟩).2.val+1*j.val=(atRef j).2.val
  simpa only [Nat.one_mul] using (good j).2.symm

variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [CommSemiring K]
variable (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (m p : ℕ) (hp : 0<p)
variable (s : Bool) (w : W) {depth n : ℕ} (book : LinkId owner s w ↪ Node depth) (key : I↪Fin n)
local notation "wt" => fun _ : I=>m*p
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "lp" => link contact owner s w
local notation "cost" => amount contact owner wt s w
local notation "N" => DescentFixedExceptionalRouter.device D contact input site owner wt s w book
local notation "code" => DescentFixedNamedContact.code book lp
local notation "X" => slotSource key contact wt input site owner align s w D
local notation "Y" => slotTarget key contact wt input site owner s w D
local notation "Z" => Contact.innerRows (D:=D) (h:=depth) (itemKey key contact owner s w) code cost
local notation "lens" => DescentNetworkSubstitution.slotWidth B (s,w)
local notation "T" => DescentFixedExceptionalRouter.Ordered.tables (K:=K) D contact input site owner wt align s w book key
local notation "pre" => previous D contact input site owner wt align s w book key
local notation "post" => following D contact input site owner wt s w book key

private theorem lane_offset (start row digit : ℕ) :
    start + (digit + row) = start + (0 + row) + digit := by omega

omit [Fintype R] in
private theorem previous_consecutive (i : Item contact owner s w) (r : Fin m) (k : Fin (depth+1)) :
    consecutive hp (fun j : Fin p=>pre i (finProdFinEquiv (r,j)) k) := by
  refine Fin.cases ?_ (fun t => ?_) k <;> intro j
  all_goals exact ⟨rfl,lane_offset _ (p*r.val) j.val⟩

omit [Fintype R] in
private theorem following_consecutive (i : Item contact owner s w) (r : Fin m) (k : Fin (depth+1)) :
    consecutive hp (fun j : Fin p=>post i (finProdFinEquiv (r,j)) k) := by
  refine Fin.lastCases ?_ (fun t => ?_) k
  · simp only [following,Fin.lastCases_last]
    intro j
    exact ⟨rfl,lane_offset _ (p*r.val) j.val⟩
  · simp only [following,Fin.lastCases_castSucc]
    intro j
    exact ⟨rfl,lane_offset _ (p*r.val) j.val⟩

private def packets (q : Physical.Site depth) (i : Cell code q.1.val q.2) (r : Fin m) :
    DescentLaneGates.Lane p (boundaryWidth N q) × DescentLaneGates.Lane p (boundaryWidth N q) := by
  let located : Physical.Site depth := ⟨q.1,prefixAt code q.1.val i.val⟩
  have position : located=q := congrArg (Sigma.mk q.1) i.property
  let pair : DescentLaneGates.Lane p (boundaryWidth N located) ×
      DescentLaneGates.Lane p (boundaryWidth N located) :=
    ⟨segment hp _ (previous_consecutive D contact input site owner align m p hp s w book key i.val r q.1),
      segment hp _ (following_consecutive D contact input site owner m p hp s w book key i.val r q.1)⟩
  exact position ▸ pair

omit [Fintype R] in
private theorem packets_read (a : (N).Assignment) (pins : Ports lens) (q : Physical.Site depth)
    (i : Cell code q.1.val q.2) (r : Fin m) (j : Fin p) :
    let pair := packets D contact input site owner align m p hp s w book key q i r
    assignmentBit N a pins q (pair.1.atBit j)=Physical.incoming cost (X pins) (Z a) q.1 i.val (finProdFinEquiv (r,j)) ∧
    assignmentBit N a pins q (pair.2.atBit j)=Physical.outgoing cost (Y pins) (Z a) q.1 i.val (finProdFinEquiv (r,j)) := by
  obtain ⟨k,node⟩:=q
  obtain ⟨i,atNode⟩:=i
  change prefixAt code k.val i=node at atNode
  subst node
  constructor
  · simpa only [packets,segment_read] using
      previous_read D contact input site owner wt align s w book key a pins i (finProdFinEquiv (r,j)) k
  · simpa only [packets,segment_read] using
      following_read D contact input site owner wt s w book key a pins i (finProdFinEquiv (r,j)) k

def program (alphabet : ℕ) (q : Physical.Site depth) : DescentLaneGates.Program alphabet p (boundaryWidth N q) where
  Node := Cell code q.1.val q.2 × Fin m
  op z := let pair:=packets D contact input site owner align m p hp s w book key q z.1 z.2
    DescentLaneGates.equalOp (.wire pair.1) (.wire pair.2)

local notation "operations" => program D contact input site owner align m p hp s w book key

omit [Fintype R] in
theorem node_count (alphabet : ℕ) (q : Physical.Site depth) :
    Fintype.card (operations alphabet q).Node*p=Physical.nodeWidth code cost q.1.val q.2 := by
  calc
    _ = Fintype.card (Cell code q.1.val q.2 × Fin m) * p :=
      congrArg (· * p) (Fintype.card_congr' rfl)
    _ = ∑ _i : Cell code q.1.val q.2, m*p := by simp [Nat.mul_assoc]

theorem node_count_bound (alphabet : ℕ) (q : Physical.Site depth) :
    Fintype.card (operations alphabet q).Node≤DescentNetworkSubstitution.portLoad N q/p := by
  apply (Nat.le_div_iff_mul_le hp).mpr
  rw [node_count]
  exact DescentFixedExceptionalRouter.nodeWidth_le_portLoad D contact input site owner wt align s w book q

omit [Fintype R] in
theorem node_arity (alphabet : ℕ) (q : Physical.Site depth) (z : (operations alphabet q).Node) :
    ((operations alphabet q).op z).arity=2 := rfl

omit [Fintype R] in
theorem stride_one (alphabet : ℕ) (q : Physical.Site depth) (z : (operations alphabet q).Node)
    (j : Fin (((operations alphabet q).op z).arity)) : (((operations alphabet q).op z).arg j).stride=1 := by
  obtain ⟨k,node⟩:=q
  obtain ⟨⟨i,atNode⟩,r⟩:=z
  change prefixAt code k.val i=node at atNode
  subst node
  change Fin 2 at j
  by_cases first : j=0 <;> simp only [program,packets,DescentLaneGates.equalOp,first,ite_true,
    ite_false,segment]

omit [Fintype R] in
/-- The product of complete lane equalities is precisely the original ordered tree table,
because each original word bit has a unique item-lane and within-lane digit. -/
theorem program_read {alphabet : ℕ} (c : Fin alphabet→Fin alphabet→ℕ) (C₀ b : ℕ)
    (rom : Fin (Fintype.card (DescentRotor.Entry c C₀ b))→K)
    (a : (N).Assignment) (pins : Ports lens) (q : Physical.Site depth) :
    (operations alphabet q).recipe.value (DescentLaneGates.scalar c C₀ b p rom)
      (DescentResetGates.assignmentBit N a pins q)=(N).read T a pins q := by
  rw [DescentLaneGates.Program.read,DescentFixedExceptionalRouter.Ordered.read]
  let check (i : Cell code q.1.val q.2) (j : Fin (m*p)) :=
    Physical.incoming cost (X pins) (Z a) q.1 i.val j=Physical.outgoing cost (Y pins) (Z a) q.1 i.val j
  have each (z : Cell code q.1.val q.2 × Fin m) :
      ((operations alphabet q).op z).value (DescentLaneGates.scalar c C₀ b p rom)
        (DescentResetGates.assignmentBit N a pins q)=if ∀j : Fin p,check z.1 (finProdFinEquiv (z.2,j)) then 1 else 0 := by
    let pair:=packets D contact input site owner align m p hp s w book key q z.1 z.2
    change (DescentLaneGates.equalOp (.wire pair.1) (.wire pair.2)).value _ _=_
    rw [DescentLaneGates.equal_read c C₀ b rom hp]
    refine if_congr ?_ rfl rfl
    rw [funext_iff]
    apply forall_congr'
    intro j
    have read := packets_read D contact input site owner align m p hp s w book key a pins q z.1 z.2 j
    change (DescentResetGates.assignmentBit N a pins q (pair.1.atBit j)=
      DescentResetGates.assignmentBit N a pins q (pair.2.atBit j)) ↔ _
    rw [read.1,read.2]
  let checks (z : (operations alphabet q).Node) :=
    ∀ j : Fin p, check z.1 (finProdFinEquiv (z.2,j))
  calc
    _ = ∏ z, (if checks z then (1 : K) else 0) :=
      congrArg (fun f : (operations alphabet q).Node → K => ∏ z, f z) (funext each)
    _ = if ∀ z, checks z then 1 else 0 := DescentResetGates.product_checks checks
    _ = _ := by
      refine if_congr ?_ rfl rfl
      constructor
      · intro allChecks i
        funext j
        obtain ⟨⟨r,t⟩,rfl⟩ := finProdFinEquiv.surjective j
        exact allChecks (i,r) t
      · intro yes z j
        exact congrFun (yes z.1) _

end
end Hierarchy.DescentTreeLaneProgram

end OAI
