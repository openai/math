import OAI.Hierarchy.DescentBatchedReentry

namespace OAI
/-! # Physical ordinal names for every atom of an installed batched reset -/

namespace Hierarchy.DescentBatchedNodeOrder
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentLaneGates DescentRotor DescentRouterSlots
open DescentPhysicalSplit DescentContactTree DescentOrderedWords DescentOrderedReset DescentMixedRouter
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section

/-- Tighten just the declared bound of an explicit ordering. Its numeric address is preserved. -/
def tight {X : Type} [Fintype X] {b : ℕ} (o : X ≃ Fin b) : X ≃ Fin (Fintype.card X) :=
  o.trans (finCongr (by simpa using (Fintype.card_congr o).symm))

/-- In any observed cell read its actual chronological packet prefix plus its batch number. -/
def cellOrder {X : Type} [Fintype X] {n : ℕ} (key : X ↪ Fin n) (m : ℕ) : X×Fin m ≃ Fin (Fintype.card (X×Fin m)) :=
  tight ((Equiv.sigmaEquivProd X (Fin m)).symm.trans (address key (fun _=>m)))

theorem cellOrder_val {X : Type} [Fintype X] {n : ℕ} (key : X ↪ Fin n) (m : ℕ) (x : X) (k : Fin m) :
    (cellOrder key m (x,k)).val=(before key x).card*m+k.val := by
  change offset key (fun _=>m) x+k.val=_
  simp [offset]

def emptyOrder : Empty≃Fin 0 := ⟨Empty.elim,Fin.elim0,fun x=>x.elim,fun x=>x.elim0⟩

def blockOrder (r m b : ℕ) : Block r m b ≃ Fin (r*(m*b)) :=
  (Equiv.prodCongr (Equiv.refl (Fin r)) finProdFinEquiv).trans finProdFinEquiv

theorem blockOrder_val {r m b : ℕ} (t : Block r m b) : (blockOrder r m b t).val=t.2.2.val+b*t.2.1.val+(m*b)*t.1.val := rfl

def tapOrder {q : ℕ} (r m : ℕ) (sub : Fin q→ℕ) (i : Fin q) :
    (SpineRow (r:=r) (m:=m) sub ⊕ Block r m (sub i)) ≃ Fin (Fintype.card (SpineRow (r:=r) (m:=m) sub ⊕ Block r m (sub i))) :=
  tight ((Equiv.sumCongr (groupOrder r m sub) (blockOrder r m (sub i))).trans finSumFinEquiv)

theorem tapOrder_spine {q : ℕ} (r m : ℕ) (sub : Fin q→ℕ) (i j : Fin q) (t : Block r m (sub j)) :
    (tapOrder r m sub i (.inl ⟨j,t⟩)).val=(∑a : Fin j,r*(m*sub (Fin.castLE j.isLt.le a)))+(t.2.2.val+sub j*t.2.1.val+(m*sub j)*t.1.val) := by
  change (finSigmaFinEquiv (n:=fun a : Fin q=>r*(m*sub a)) ⟨j,blockOrder r m (sub j) t⟩).val=_
  rw [finSigmaFinEquiv_apply,blockOrder_val]

theorem tapOrder_selected {q : ℕ} (r m : ℕ) (sub : Fin q→ℕ) (i : Fin q) (t : Block r m (sub i)) :
    (tapOrder r m sub i (.inr t)).val=(∑a,r*(m*sub a))+(t.2.2.val+sub i*t.2.1.val+(m*sub i)*t.1.val) := rfl

variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits M : ℕ} (G : Graph n h) (hw : 0<bits) (m p : ℕ) (hp : 0<p)
variable (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (key : I↪Fin M) (D : ℕ) {s : Bool} {w : W}
local notation "u" => m*p
local notation "wt" => (fun _ : I=>u)
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align
local notation "A" => device G hw u contact input site owner align (D:=D)
local notation "prog" => DescentBatchedBank.deviceProgram G hw m p hp contact input site owner align key D

/-- Root order is (layer, batch), reflected by the two fields of the installed circuit. A tap's
first range contains the true whole-spine lanes and the second its one selected row. -/
def deviceOrder : (z : Ch s w)→(v : (A z).Site)→(prog z v).Node ≃ Fin (Fintype.card (prog z v).Node)
  | .exceptional d,⟨k,q⟩=>
    let dest:=DescentFixedNamedContact.code d.book.codes (link contact owner s w)
    let items:=itemKey key contact owner s w
    cellOrder (Contact.cellKey items dest k.val q) m
  | .good _ _ _ _,⟨_,.inl false⟩=>tight finProdFinEquiv
  | .good _ _ _ _,⟨_,.inl true⟩=>tight emptyOrder
  | .good _ _ _ P,⟨v,.inr i⟩=>tapOrder P.layers m (tapBits D u G P v) i

omit [Fintype R] in
theorem root_number (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n)) (pay : ℝ)
    (P : BaseCircuit K G C₀ bits u hw (fun e=>first (root contact input site owner s w align e))
      (fun e=>last (link contact owner s w e)) pay) (v : Fin (2^n)) (r : Fin P.layers) (batch : Fin m) :
    (deviceOrder G hw m p hp contact input site owner align key D (.good first last pay P) ⟨v,.inl false⟩ (r,batch)).val=
      m*r.val+batch.val := by change batch.val+m*r.val=_;omega

omit [Fintype R] in
theorem tree_number (z : ExceptionalData (InputId site s w) (LinkId owner s w))
    (q : DescentContactTree.Physical.Site z.book.height)
    (i : Cell (DescentFixedNamedContact.code z.book.codes (link contact owner s w)) q.1.val q.2) (batch : Fin m) :
    (deviceOrder (K:=K) (C₀:=C₀) (s:=s) (w:=w) G hw m p hp contact input site owner align key D (.exceptional z) q (i,batch)).val=
      (Finset.univ.filter (fun j : Cell (DescentFixedNamedContact.code z.book.codes (link contact owner s w)) q.1.val q.2 =>
        key j.val.val < key i.val.val)).card*m+batch.val :=
  cellOrder_val _ _ _ _

variable (sel : ∀s w,Choice (K:=K) (C₀:=C₀) G hw (m*p) contact input site owner align s w)
local notation "bank" => DescentMixedRouter.network (K:=K) (C₀:=C₀) G hw (m*p) contact input site owner align sel D
local notation "bankAt" => DescentBatchedBank.program (K:=K) (C₀:=C₀) G hw m p hp contact input site owner align key D sel

def bankOrder (v : (bank).Site) : (bankAt v).Node ≃ Fin (Fintype.card (bankAt v).Node) :=
  deviceOrder G hw m p hp contact input site owner align key D (sel v.1.1 v.1.2) v.2

variable (u₀ : ℕ) (fit : u₀=m*p)
variable (sel₀ : ∀s w,Choice (K:=K) (C₀:=C₀) G hw u₀ contact input site owner align s w)
local notation "actual" => DescentMixedRouter.network G hw u₀ contact input site owner align sel₀ D
local notation "actualAt" => DescentBatchedBank.sizedProgram G hw u₀ m p hp fit contact input site owner align key D sel₀

def sizedOrder (v : (actual).Site) : (actualAt v).Node ≃ Fin (Fintype.card (actualAt v).Node) := by
  subst u₀
  exact bankOrder G hw m p hp contact input site owner align key D sel₀ v
end
end Hierarchy.DescentBatchedNodeOrder

namespace Hierarchy.DescentSixParty.ResetInput
open DescentKernelHistory DescentChosenRouter
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht L : ℕ} (Z : ResetInput A price ε h C Ht) (key : A.graph.Edge↪Fin L)
variable (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
local notation "R" => Z.placement
local notation "S" => DescentChosenRouter.selected R Z.graph Z.positive Z.pay Z.circuit
local notation "atSite" => Z.laneProgram key m p hp fit

def laneNodeOrder (v : Z.bank.Site) : (atSite v).Node ≃ Fin (Fintype.card (atSite v).Node) :=
  DescentBatchedNodeOrder.sizedOrder Z.graph Z.positive m p hp (R).contact (R).input (R).site (R).owner (R).align key d Z.unit fit S v

def nodeIndex (v : Z.bank.Site) : (atSite v).Node ↪ ℕ := (Z.laneNodeOrder key m p hp fit v).toEmbedding.trans Fin.valEmbedding

theorem nodeIndex_bound (v : Z.bank.Site) (i : (atSite v).Node) : Z.nodeIndex key m p hp fit v i <
    (2*DescentNetworkSubstitution.portLoad Z.bank v)/p :=
  ((Z.laneNodeOrder key m p hp fit v i).isLt).trans_le
    ((Nat.le_div_iff_mul_le hp).mpr (Z.lane_count_mul_le key m p hp fit v))

/-- The ordinal cell in the terminal instruction tape reads the very same atom and no other. -/
theorem nodeIndex_read (v : Z.bank.Site) (i : (atSite v).Node) :
    (atSite v).op ((Z.laneNodeOrder key m p hp fit v).symm (Z.laneNodeOrder key m p hp fit v i))=(atSite v).op i :=
  congrArg (atSite v).op ((Z.laneNodeOrder key m p hp fit v).symm_apply_apply i)

/-- Finite installed gate tape in that explicit order. Each entry includes the actual opcode and all affine operands. -/
def laneTape (v : Z.bank.Site) := List.ofFn ((atSite v).op ∘ (Z.laneNodeOrder key m p hp fit v).symm)

@[simp] theorem laneTape_length (v : Z.bank.Site) : (Z.laneTape key m p hp fit v).length=Fintype.card (atSite v).Node := by
  simp [laneTape]

theorem laneTape_read (v : Z.bank.Site) (i : (atSite v).Node) :
    (Z.laneTape key m p hp fit v)[Z.nodeIndex key m p hp fit v i]'(by
      rw [laneTape_length];exact (Z.laneNodeOrder key m p hp fit v i).isLt)=(atSite v).op i := by
  simp [laneTape,nodeIndex,Function.comp_def]

def laneHiddenOrder (v : Z.bank.Site) : (Z.laneRecipe key m p hp fit v).Hidden ≃ Fin 0 := DescentBatchedNodeOrder.emptyOrder

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
