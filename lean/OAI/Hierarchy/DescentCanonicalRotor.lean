import OAI.Hierarchy.DescentOrderedRotorTapRefs
import OAI.Hierarchy.DescentCanonicalScalars
import OAI.Hierarchy.DescentSubstitutionDegree

namespace OAI
/-! # The fixed ROM and literal bit equalities at each installed ordered rotor site -/

namespace Hierarchy.DescentCanonicalRotor
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open Computability.BorderVNP.Crossing DescentRotor DescentResetGates DescentPhysicalSplit DescentKernelHistory DescentRouterSlots
open private DescentRotor.regular_ports from OAI.Hierarchy.DescentRotorHost
open private DescentResetGates.rotorPortWidth DescentResetGates.rotorAssignmentBit from OAI.Hierarchy.DescentOrderedRotorTapRefs
open scoped Classical BigOperators
noncomputable section
section Spine
variable {d : ℕ} {T Q : Type} [Fintype T] {bitsAt : T → ℕ} (host : Network d T bitsAt)
    (place : Q → T) (widths : Q → ℕ)

private theorem spine_target (v : host.Site) (i : Fin (count host v)) :
    (DescentPhysicalSplit.graph host).dst (.inr ⟨v,i.castSucc⟩) = ⟨v,.inr i⟩ := by
  change (⟨v,Attachment.nextSite i.castSucc⟩ : DescentPhysicalSplit.Vertex host) = ⟨v,.inr i⟩
  simp [Attachment.nextSite]

private def leftRef (v : host.Site) (i : Fin (count host v)) (j : Fin (∑ t, localWidth host v t)) :
    BitRef (DescentResetGates.rotorPortWidth host place widths ⟨v,.inr i⟩) :=
  ⟨.inl ⟨.inr ⟨v,i.castSucc⟩,Or.inr (spine_target host v i)⟩,j⟩

private def rightRef (v : host.Site) (i : Fin (count host v)) (j : Fin (∑ t, localWidth host v t)) :
    BitRef (DescentResetGates.rotorPortWidth host place widths ⟨v,.inr i⟩) :=
  ⟨.inl ⟨.inr ⟨v,i.succ⟩,Or.inl rfl⟩,j⟩
end Spine

variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable (D u : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {n h b C₀ m : ℕ}
    (G : Graph n h) {hw : 0<b} {pay : ℝ} (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
local notation "wt" => (fun _ : I=>u)
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "lens" => DescentNetworkSubstitution.slotWidth B (s,w)
variable (P : BaseCircuit K G C₀ b u hw
    (fun e : Item contact owner s w => first (root contact input site owner s w align e))
    (fun e : Item contact owner s w => last (link contact owner s w e)) pay) (key : I↪Fin m)
local notation "H" => Physical.host G.arcs D P.layers C₀ b u
local notation "A" => DescentGoodRouter.device D u contact input site owner align s w G first last P
local notation "T" => DescentGoodRouter.Ordered.tables D u contact input site owner align s w G first last P key
local notation "pinsAt" => DescentGoodRouter.Ordered.pins D u contact input site owner align s w G first last P key
local notation "sideAt" => tapLegSource D u contact input site owner align s w G first last P key

local notation "positionAt" => DescentGoodRouter.position D u contact input site owner s w first last
local notation "splitDevice" => DescentLocalAdapters.graph (DescentPhysicalSplit.graph H) positionAt lens
local notation "widthAt" => DescentResetGates.rotorPortWidth H positionAt lens
local notation "readAt" => DescentResetGates.rotorAssignmentBit H positionAt lens
local notation "leftCable" => leftRef H positionAt lens
local notation "rightCable" => rightRef H positionAt lens

def program : (q : DescentPhysicalSplit.Vertex H)→Program (2^n) (widthAt q)
  | ⟨v,.inl false⟩=>{
      Node:=Fin P.layers × Fin u
      op i:=rotorOp G.arcs C₀ b (P.rotation i.1) v (fun p j=>⟨.inl ⟨.inr ⟨v,0⟩,Or.inl rfl⟩,rootColumn G P D v i.1 i.2 p j⟩) }
  | ⟨_,.inl true⟩=>{Node:=Empty,op:=Empty.elim}
  | ⟨v,.inr i⟩=>{
      Node:=Fin (∑t,localWidth H v t) ⊕ Fin (localWidth H v i)
      op:=Sum.elim (fun j=>equalOp (.bit (leftCable v i j)) (.bit (rightCable v i j)))
        (fun j=>equalOp (.bit (leftCable v i (finSigmaFinEquiv ⟨i,j⟩))) (sideAt v i j)) }

local notation "prg" => program D u contact input site owner align s w G first last P key
theorem operand_sum (v : Fin (2^n)) : (∑j,SlotWidth G.arcs C₀ b v j)=(2+2*h*C₀)*b := by
  rw [Fintype.sum_sum_type]
  simp [SlotWidth,DescentRotor.regular_ports]
  ring

private theorem roster_sum {α : Type} {t u : Fintype α} (f : α → ℕ) :
    (@Finset.univ α t).sum f = (@Finset.univ α u).sum f := by
  cases Subsingleton.elim t u
  rfl

omit [Fintype R] in
private theorem root_node_bits (v : Fin (2^n)) (i : Fin P.layers × Fin u) :
    ((prg ⟨v,.inl false⟩).op i).bitCount = ∑p,SlotWidth G.arcs C₀ b v p := by
  let row : (p : Slot G.arcs v) → Fin (SlotWidth G.arcs C₀ b v p) → BitRef (widthAt ⟨v,.inl false⟩) :=
    fun p j => ⟨.inl ⟨.inr ⟨v,0⟩, Or.inl rfl⟩, rootColumn G P D v i.1 i.2 p j⟩
  change (rotorOp G.arcs C₀ b (P.rotation i.1) v row).bitCount = _
  exact (rotorOp_bits G.arcs C₀ b (P.rotation i.1) v row).trans (roster_sum (SlotWidth G.arcs C₀ b v))

omit [Fintype R] in
theorem node_bits (q : DescentPhysicalSplit.Vertex H) (i : (prg q).Node) : ((prg q).op i).bitCount≤ max 2 ((2+2*h*C₀)*b) := by
  rcases q with ⟨v,(_|_)|j⟩
  · exact ((root_node_bits D u contact input site owner align s w G first last P key v i).trans
      (operand_sum (C₀:=C₀) (b:=b) G v)).le.trans (Nat.le_max_right _ _)
  · exact i.elim
  · rcases i with i|i
    · exact (equalOp_bits (width:=widthAt ⟨v,.inr j⟩) (Y:=2^n) (.bit (leftCable v j i)) (.bit (rightCable v j i))).trans (Nat.le_max_left _ _)
    · exact (equalOp_bits (width:=widthAt ⟨v,.inr j⟩) (Y:=2^n) (.bit (leftCable v j (finSigmaFinEquiv ⟨j,i⟩))) (sideAt v j i)).trans
        (Nat.le_max_left _ _)

omit [Fintype R] in
theorem node_arity (q : DescentPhysicalSplit.Vertex H) (i : (prg q).Node) : ((prg q).op i).arity≤2*h+2 := by
  rcases q with ⟨v,(_|_)|j⟩
  · exact (regular_slots G v).le
  · exact i.elim
  · have room : 2 ≤ 2*h+2 := Nat.le_add_left ..
    rcases i with i|i
    · exact (equalOp_arity (width:=widthAt ⟨v,.inr j⟩) (Y:=2^n) (.bit (leftCable v j i)) (.bit (rightCable v j i))).trans room
    · exact (equalOp_arity (width:=widthAt ⟨v,.inr j⟩) (Y:=2^n) (.bit (leftCable v j (finSigmaFinEquiv ⟨j,i⟩))) (sideAt v j i)).trans room

private theorem card_le_positive_sum {α : Type} [Fintype α] (f : α → ℕ)
    (pos : ∀ i, 1 ≤ f i) : Fintype.card α ≤ ∑ i, f i :=
  calc
    Fintype.card α = ∑ _ : α, 1 := by simp
    _ ≤ ∑ i, f i := Finset.sum_le_sum (fun i _ => pos i)

omit [Fintype R] in
theorem root_bits (v : Fin (2^n)) : (∑i : (prg ⟨v,.inl false⟩).Node,((prg ⟨v,.inl false⟩).op i).bitCount)=(DescentPhysicalSplit.graph H).width (.inr ⟨v,0⟩) := by
  let rows : (prg ⟨v,.inl false⟩).Node ≃ Fin P.layers × Fin u := Equiv.refl _
  calc
    _ = ∑ _ : Fin P.layers × Fin u, ∑ p, SlotWidth G.arcs C₀ b v p :=
      Fintype.sum_equiv rows _ _ (fun i =>
        root_node_bits D u contact input site owner align s w G first last P key v i)
    _ = _ := allRootBits G P D v

omit [Fintype R] in
theorem tap_nodes (v : Fin (2^n)) (j : Fin (count H v)) :
    Fintype.card (prg ⟨v,.inr j⟩).Node=(DescentPhysicalSplit.graph H).width (.inr ⟨v,j.castSucc⟩)+localWidth H v j := by
  let rows : (prg ⟨v,.inr j⟩).Node ≃
      Fin (∑ t,localWidth H v t) ⊕ Fin (localWidth H v j) := Equiv.refl _
  calc
    _ = Fintype.card (Fin (∑ t,localWidth H v t) ⊕ Fin (localWidth H v j)) :=
      Fintype.card_congr rows
    _ = (∑ t,localWidth H v t) + localWidth H v j := by
      simp only [Fintype.card_sum, Fintype.card_fin]
    _ = _ := rfl

omit [Fintype R] in
theorem blank_nodes (v : Fin (2^n)) : Fintype.card (prg ⟨v,.inl true⟩).Node=0 := rfl

set_option maxHeartbeats 1000000 in
theorem node_count_le (q : DescentPhysicalSplit.Vertex H) : Fintype.card (prg q).Node≤2*DescentNetworkSubstitution.portLoad splitDevice q := by
  rcases q with ⟨v,(_|_)|j⟩
  · have one := Finset.single_le_sum (s:=Finset.univ) (f:=SlotWidth G.arcs C₀ b v)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (.inl false))
    change b ≤ _ at one
    let rows : (prg ⟨v,.inl false⟩).Node ≃ Fin P.layers × Fin u := Equiv.refl _
    have two : Fintype.card (prg ⟨v,.inl false⟩).Node ≤ (DescentPhysicalSplit.graph H).width (.inr ⟨v,0⟩) := calc
      _ = Fintype.card (Fin P.layers × Fin u) := Fintype.card_congr rows
      _ ≤ ∑ _ : Fin P.layers × Fin u, ∑ t, SlotWidth G.arcs C₀ b v t :=
        card_le_positive_sum (fun _ : Fin P.layers × Fin u => ∑ t, SlotWidth G.arcs C₀ b v t)
          (fun _ => (Nat.succ_le_of_lt hw).trans one)
      _ = _ := by
        refine Eq.trans ?_ (allRootBits G P D v)
        exact Finset.sum_congr rfl (fun _ _ => roster_sum (SlotWidth G.arcs C₀ b v))
    have port : (DescentPhysicalSplit.graph H).width (.inr ⟨v,0⟩) ≤
        DescentNetworkSubstitution.portLoad splitDevice ⟨v,.inl false⟩ :=
      DescentNetworkSubstitution.cable_width_le_portLoad splitDevice ⟨v,.inl false⟩ (.inr ⟨v,0⟩) (Or.inl rfl)
    exact (two.trans (port.trans (Nat.le_add_right ..))).trans_eq (two_mul _).symm
  · exact (blank_nodes D u contact input site owner align s w G first last P key v).le.trans (Nat.zero_le _)
  · have port : (DescentPhysicalSplit.graph H).width (.inr ⟨v,j.castSucc⟩) ≤
        DescentNetworkSubstitution.portLoad splitDevice ⟨v,.inr j⟩ :=
      DescentNetworkSubstitution.cable_width_le_portLoad splitDevice ⟨v,.inr j⟩ (.inr ⟨v,j.castSucc⟩)
        (Or.inr (spine_target H v j))
    have small := Finset.single_le_sum (s:=Finset.univ) (f:=localWidth H v)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    change localWidth H v j ≤ (DescentPhysicalSplit.graph H).width (.inr ⟨v,j.castSucc⟩) at small
    exact (tap_nodes D u contact input site owner align s w G first last P key v j).le.trans
      ((Nat.add_le_add port (small.trans port)).trans_eq (two_mul _).symm)

variable (menu : ∀π,Configures K G.arcs C₀ b π)
local notation "romWord" => rom G.arcs C₀ b (fixedTable menu)
local notation "scalar" => canonicalScalar G.arcs C₀ b romWord

private theorem equal_test {α : Type} {p q : Prop} {dp : Decidable p} {dq : Decidable q}
    (yes no : α) (agree : p ↔ q) : @ite α p dp yes no = @ite α q dq yes no := by
  cases dp with
  | isTrue hp =>
    cases dq with
    | isTrue hq => rfl
    | isFalse hq => exact (hq (agree.mp hp)).elim
  | isFalse hp =>
    cases dq with
    | isTrue hq => exact (hp (agree.mpr hq)).elim
    | isFalse hq => rfl

set_option maxHeartbeats 1200000 in
omit [Fintype R] in
theorem program_read (a : (DescentPhysicalSplit.graph H).Assignment) (p : Ports lens) (q : DescentPhysicalSplit.Vertex H) :
    (prg q).recipe.value scalar (readAt a p q)=(A).read T a p q := by
  have adapter : (A).read T a p q =
      (Physical.rotor G P D).read (Physical.rotorTables G P D) a (pinsAt p) q :=
    DescentLocalAdapters.read (Physical.rotor G P D) positionAt lens (Physical.rotorTables G P D) pinsAt
      (DescentGoodRouter.Ordered.local_pins D u contact input site owner align s w G first last P key) a p q
  refine (Program.value (prg q) scalar (readAt a p q)).trans (Eq.trans ?_ adapter.symm)
  rcases q with ⟨v,(_|_)|i⟩
  · refine Eq.trans ?_ ((rotor_correct G P D menu) a (pinsAt p) ⟨v,.inl false⟩).symm
    change (∏ t : Fin P.layers × Fin u, ((prg ⟨v,.inl false⟩).op t).value scalar
      (readAt a p ⟨v,.inl false⟩)) =
      ∏ t : Fin P.layers × Fin u, romWord (rootAddress G P D v (tuple H v (a (.inr ⟨v,0⟩))) t.1 t.2)
    apply Finset.prod_congr rfl
    rintro ⟨r,k⟩ _
    let refs : (z : Slot G.arcs v) → Fin (SlotWidth G.arcs C₀ b v z) → BitRef (widthAt ⟨v,.inl false⟩) :=
      fun z j => ⟨.inl ⟨.inr ⟨v,0⟩,Or.inl rfl⟩,rootColumn G P D v r k z j⟩
    exact (rotorOp_read G.arcs C₀ b romWord (P.rotation r) v refs (readAt a p ⟨v,.inl false⟩)).trans
      (congrArg romWord (rootKey_read G P D v r k (a (.inr ⟨v,0⟩))))
  · refine Eq.trans ?_ (DescentPhysicalSplit.read_eq H (Physical.hostTables G.arcs P.tables) a (pinsAt p)
      ⟨v,.inl true⟩).symm
    change (∏ j : Empty, ((prg ⟨v,.inl true⟩).op j).value scalar (readAt a p ⟨v,.inl true⟩)) = 1
    simp
  · refine Eq.trans ?_ (DescentPhysicalSplit.read_eq H (Physical.hostTables G.arcs P.tables) a (pinsAt p)
      ⟨v,.inr i⟩).symm
    let left := a (.inr ⟨v,i.castSucc⟩)
    let right := a (.inr ⟨v,i.succ⟩)
    let x := args H (decode H a).1 (pinsAt p) v i
    let pred : (Fin (∑ t,localWidth H v t) ⊕ Fin (localWidth H v i)) → Prop :=
      Sum.elim (fun j => left j = right j) (fun j => left (finSigmaFinEquiv ⟨i,j⟩) = x j)
    have op (j : Fin (∑ t,localWidth H v t) ⊕ Fin (localWidth H v i)) :
        ((prg ⟨v,.inr i⟩).op j).value scalar (readAt a p ⟨v,.inr i⟩) = if pred j then 1 else 0 := by
      rcases j with j|j
      · exact (equalOp_read G.arcs C₀ b romWord (.bit (leftCable v i j)) (.bit (rightCable v i j))
          (readAt a p ⟨v,.inr i⟩)).trans (equal_test (1:K) 0 Iff.rfl)
      · let c := finSigmaFinEquiv (⟨i,j⟩ : (s : Fin (count H v)) × Fin (localWidth H v s))
        have seen := tapLegSource_read D u contact input site owner align s w G first last P key a p v i j
        refine (equalOp_read G.arcs C₀ b romWord (.bit (leftCable v i c)) (sideAt v i j)
          (readAt a p ⟨v,.inr i⟩)).trans (equal_test (1:K) 0 ?_)
        change (left c = (sideAt v i j).read (readAt a p ⟨v,.inr i⟩)) ↔ left c = x j
        exact ⟨fun e => e.trans seen, fun e => e.trans seen.symm⟩
    let rows : (prg ⟨v,.inr i⟩).Node ≃
        Fin (∑ t,localWidth H v t) ⊕ Fin (localWidth H v i) := Equiv.refl _
    refine (Fintype.prod_equiv rows _ (fun j => if pred j then (1 : K) else 0)
      (fun j => op (rows j))).trans ((product_checks (K:=K) pred).trans ?_)
    have law : (∀ j,pred j) ↔ tuple H v left = tuple H v right ∧ tuple H v left i = x := by
      constructor
      · intro all
        exact ⟨congrArg (tuple H v) (funext fun j => all (.inl j)),funext fun j => all (.inr j)⟩
      · rintro ⟨both,row⟩ (j|j)
        · exact congrFun ((tuple H v).injective both) j
        · exact congrFun row j
    exact equal_test (1:K) 0 law

end
end Hierarchy.DescentCanonicalRotor

end OAI
