import OAI.Hierarchy.DescentCanonicalScalars
import OAI.Hierarchy.DescentOrderedExceptionalRouter

namespace OAI
/-! # Actual ordered bit pairs at the vertices of the exceptional reset trees -/

namespace Hierarchy.DescentTreeGateRefs
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRouterSlots DescentContactTree
open DescentOrderedReset DescentOrderedWords
open scoped Classical BigOperators
noncomputable section
open private DescentFixedNamedContact.prefix_eq from OAI.Hierarchy.DescentFixedNamedContact
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [CommSemiring K]
variable (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W) (wt : I→ℕ)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {depth n : ℕ}
    (book : LinkId owner s w ↪ Node depth) (key : I↪Fin n)
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "lp" => link contact owner s w
local notation "cost" => amount contact owner wt s w
local notation "N" => DescentFixedExceptionalRouter.device D contact input site owner wt s w book
local notation "ids" => itemKey key contact owner s w
local notation "d" => DescentFixedNamedContact.code book lp
local notation "X" => slotSource key contact wt input site owner align s w D
local notation "Y" => slotTarget key contact wt input site owner s w D
local notation "Z" => Contact.innerRows (D:=D) (h:=depth) ids d cost
local notation "lens" => DescentNetworkSubstitution.slotWidth B (s,w)
local notation "T" => DescentFixedExceptionalRouter.Ordered.tables (K:=K) D contact input site owner wt align s w book key

private def childBit (k : Fin depth) (i : Item contact owner s w) (j : Fin (cost i)) :=
  bitIndex (Contact.cellKey ids d (k.val+1) (prefixAt d (k.val+1) i)) (fun t=>cost t.val) ⟨⟨i,rfl⟩,j⟩

def previous (i : Item contact owner s w) (j : Fin (cost i)) :
    (k : Fin (depth+1))→BitRef (boundaryWidth N ⟨k,prefixAt d k.val i⟩) :=
  Fin.cases (⟨.inr ⟨rootSlot D contact input site owner wt s w (root contact input site owner s w align i),by
    change (⟨0,finZeroElim⟩ : Physical.Site depth) = ⟨0,prefixAt d 0 i⟩
    exact congrArg (fun v : Node 0 => (⟨0,v⟩ : Physical.Site depth))
      (Subsingleton.elim finZeroElim (prefixAt d 0 i))⟩,sourceAt key contact wt input owner s w i j⟩)
    (fun k=>⟨.inl ⟨⟨k,prefixAt d (k.val+1) i⟩,Or.inr rfl⟩,childBit contact owner wt s w book key k i j⟩)

def following (i : Item contact owner s w) (j : Fin (cost i)) :
    (k : Fin (depth+1))→BitRef (boundaryWidth N ⟨k,prefixAt d k.val i⟩) :=
  Fin.lastCases (⟨.inr ⟨linkSlot D contact input site owner wt s w (lp i),by
    change (Physical.graph d cost D depth).attach (DescentFixedNamedContact.place book (DescentExceptionalRouter.position D contact input site owner wt s w _))=_
    simp [DescentExceptionalRouter.position,DescentFixedNamedContact.place,Physical.graph,DescentFixedNamedContact.prefix_eq]⟩,
    Fin.cast (linkWidth D contact input site owner wt s w _).symm (linkAt key contact wt owner s w i j)⟩)
    (fun k=>⟨.inl ⟨⟨k,prefixAt d (k.val+1) i⟩,Or.inl rfl⟩,childBit contact owner wt s w book key k i j⟩)

omit [Fintype R] in
theorem previous_read (a : (N).Assignment) (p : Ports lens) (i : Item contact owner s w) (j : Fin (cost i)) (k : Fin (depth+1)) :
    assignmentBit N a p _ (previous D contact input site owner wt align s w book key i j k) =
      Physical.incoming cost (X p) (Z a) k i j := by
  refine Fin.cases ?_ (fun k=>?_) k <;> rfl

omit [Fintype R] in
theorem following_read (a : (N).Assignment) (p : Ports lens) (i : Item contact owner s w) (j : Fin (cost i)) (k : Fin (depth+1)) :
    assignmentBit N a p _ (following D contact input site owner wt s w book key i j k) =
      Physical.outgoing cost (Y p) (Z a) k i j := by
  refine Fin.lastCases ?_ (fun t => ?_) k
  · have edge : Physical.outgoing cost (Y p) (Z a) (Fin.last depth) = Y p :=
      @Fin.lastCases_last depth (fun _ => Physical.Row cost) (Y p) (Z a)
    rw [edge]
    simp only [following,Fin.lastCases_last]; rfl
  · have edge : Physical.outgoing cost (Y p) (Z a) t.castSucc = Z a t :=
      @Fin.lastCases_castSucc depth (fun _ => Physical.Row cost) (Y p) (Z a) t
    rw [edge]
    simp only [following,Fin.lastCases_castSucc]; rfl

private def both (q : Physical.Site depth) (i : Cell d q.1.val q.2) (j : Fin (cost i.val)) :
    BitRef (boundaryWidth N q) × BitRef (boundaryWidth N q) := by
  let located : Physical.Site depth := ⟨q.1,prefixAt d q.1.val i.val⟩
  have position : located = q := by
    exact congrArg (Sigma.mk q.1) i.property
  let pair : BitRef (boundaryWidth N located) × BitRef (boundaryWidth N located) :=
    (previous D contact input site owner wt align s w book key i.val j q.1,
      following D contact input site owner wt s w book key i.val j q.1)
  exact position ▸ pair

def program (Y₀ : ℕ) (q : Physical.Site depth) : Program Y₀ (boundaryWidth N q) where
  Node := Σi : Cell d q.1.val q.2,Fin (cost i.val)
  op z := let t:=both D contact input site owner wt align s w book key q z.1 z.2
    equalOp (.bit t.1) (.bit t.2)

omit [Fintype R] in
theorem node_count (L : ℕ) (q : Physical.Site depth) :
    Fintype.card (program D contact input site owner wt align s w book key L q).Node=Physical.nodeWidth d cost q.1.val q.2 := by
  calc
    _ = Fintype.card (Σ i : Cell d q.1.val q.2, Fin (cost i.val)) := Fintype.card_congr' rfl
    _ = ∑ i : Cell d q.1.val q.2, cost i.val := by simp only [Fintype.card_sigma,Fintype.card_fin]

omit [Fintype R] in
theorem node_bits (L : ℕ) (q : Physical.Site depth) (i : (program D contact input site owner wt align s w book key L q).Node) :
    ((program D contact input site owner wt align s w book key L q).op i).bitCount=2 := by
  exact (show (∑ _ : Fin 2, (1 : ℕ)) = 2 by simp)

omit [Fintype R] in
theorem node_arity (L : ℕ) (q : Physical.Site depth) (i : (program D contact input site owner wt align s w book key L q).Node) :
    ((program D contact input site owner wt align s w book key L q).op i).arity=2 := rfl

omit [Fintype R] in
/-- Exact site instructions, each comparing one named physical bit on either side of this relay. -/
theorem program_read {L : ℕ} (c : Fin L→Fin L→ℕ) (C₀ b : ℕ) (rom : Fin (Fintype.card (DescentRotor.Entry c C₀ b))→K)
    (a : (N).Assignment) (p : Ports lens) (q : Physical.Site depth) :
    (program D contact input site owner wt align s w book key L q).recipe.value (canonicalScalar c C₀ b rom)
      (assignmentBit N a p q)=(N).read T a p q := by
  rw [Program.value,DescentFixedExceptionalRouter.Ordered.read]
  have test (z : Σi : Cell d q.1.val q.2,Fin (cost i.val)) :
      ((program D contact input site owner wt align s w book key L q).op z).value (canonicalScalar c C₀ b rom) (assignmentBit N a p q) =
        if Physical.incoming cost (X p) (Z a) q.1 z.1.val z.2=Physical.outgoing cost (Y p) (Z a) q.1 z.1.val z.2 then 1 else 0 := by
    obtain ⟨k,node⟩:=q
    obtain ⟨⟨i,atNode⟩,j⟩:=z
    change Fin (cost i) at j
    change prefixAt d k.val i=node at atNode
    subst node
    simp only [program,both,equalOp_read,Source.read,previous_read,following_read]
  let checks (z : (program D contact input site owner wt align s w book key L q).Node) :=
    Physical.incoming cost (X p) (Z a) q.1 z.1.val z.2 =
      Physical.outgoing cost (Y p) (Z a) q.1 z.1.val z.2
  calc
    _ = ∏ z, (if checks z then (1 : K) else 0) :=
      congrArg (fun f : (program D contact input site owner wt align s w book key L q).Node → K =>
        ∏ z, f z) (funext (fun z => test z))
    _ = if ∀ z, checks z then 1 else 0 := product_checks checks
    _ = _ := by
      refine if_congr ?_ rfl rfl
      constructor
      · intro h i; exact funext fun j => h ⟨i,j⟩
      · intro h z; exact congrFun (h z.1) z.2

end
end Hierarchy.DescentTreeGateRefs

end OAI
