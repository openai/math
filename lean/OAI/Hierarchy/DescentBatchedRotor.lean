import OAI.Hierarchy.DescentCanonicalRotor
import OAI.Hierarchy.DescentOrderedRotorTapLanes
import OAI.Hierarchy.DescentLaneTranspose

namespace OAI
/-! # Actual powered rotor calls and tap comparisons, per batch of carried digits -/

namespace Hierarchy.DescentBatchedRotor
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open Computability.BorderVNP.Crossing DescentRotor DescentResetGates DescentPhysicalSplit DescentKernelHistory DescentRouterSlots
open DescentLaneGates
open private DescentResetGates.rotorPortWidth DescentResetGates.rotorAssignmentBit from OAI.Hierarchy.DescentOrderedRotorTapRefs
open private DescentCanonicalRotor.spine_target DescentCanonicalRotor.equal_test DescentCanonicalRotor.roster_sum from OAI.Hierarchy.DescentCanonicalRotor
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable (D m p : ℕ) (hp : 0<p) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {n h b C₀ num : ℕ}
    (G : Graph n h) {hw : 0<b} {pay : ℝ} (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
local notation "wt" => (fun _ : I=>(m*p))
local notation "base" => DescentRouterBank.network D contact input site owner wt
local notation "lens" => DescentNetworkSubstitution.slotWidth base (s,w)
variable (P : BaseCircuit K G C₀ b (m*p) hw
    (fun e : Item contact owner s w => first (root contact input site owner s w align e))
    (fun e : Item contact owner s w => last (link contact owner s w e)) pay) (key : I↪Fin num)
local notation "H" => Physical.host G.arcs D P.layers C₀ b (m*p)
local notation "A" => DescentGoodRouter.device D (m*p) contact input site owner align s w G first last P
local notation "positionAt" => DescentGoodRouter.position D (m*p) contact input site owner s w first last
local notation "splitDevice" => DescentLocalAdapters.graph (DescentPhysicalSplit.graph H) positionAt lens
local notation "widthAt" => DescentResetGates.rotorPortWidth H positionAt lens
local notation "readAt" => DescentResetGates.rotorAssignmentBit H positionAt lens
local notation "T" => DescentGoodRouter.Ordered.tables D (m*p) contact input site owner align s w G first last P key
local notation "pinsAt" => DescentGoodRouter.Ordered.pins D (m*p) contact input site owner align s w G first last P key
local notation "slotBits" => tapBits D (m*p) G P
local notation "legWidth" => localWidth H
local notation "shape" => tapWidth_eq D (m*p) G P
local notation "outer" => tapLegLane D (m*p) contact input site owner align s w G first last P key (m:=m) (p:=p) rfl hp
local notation "legacy" => DescentCanonicalRotor.program D (m*p) contact input site owner align s w G first last P key

private theorem flat_digit_slope (off w j d p k m r : ℕ) :
    off + (j + w*(d+p*k) + ((m*p)*w)*r) =
    off + (j + w*(0+p*k) + ((m*p)*w)*r) + w*d := by ring

include hp in
omit [Fintype C] [Fintype R] [Fintype W] in
private theorem root_slope (v : Fin (2^n)) (r : Fin P.layers) (k : Fin m) (t : RowBit G.arcs C₀ b v) (d : Fin p) :
    (rootColumn G P D v r (finProdFinEquiv (k,d)) t.1 t.2).val=
      (rootColumn G P D v r (finProdFinEquiv (k,⟨0,hp⟩)) t.1 t.2).val+SlotWidth G.arcs C₀ b v t.1*d.val := by
  rcases t with ⟨(z|z),j⟩ <;> simp only [rootColumn,tupleBit,finSigmaFinEquiv_apply]
  · exact flat_digit_slope _ b j.val d.val p k.val m r.val
  · exact flat_digit_slope _ (C₀*b) j.val d.val p k.val m r.val

include hp in
def rootLane (v : Fin (2^n)) (r : Fin P.layers) (k : Fin m) (t : RowBit G.arcs C₀ b v) : Lane p (widthAt ⟨v,.inl false⟩) :=
  affine hp (.inl ⟨.inr ⟨v,0⟩,Or.inl rfl⟩) (fun d=>rootColumn G P D v r (finProdFinEquiv (k,d)) t.1 t.2)
    (SlotWidth G.arcs C₀ b v t.1) (root_slope D m p hp contact input site owner align s w G first last P v r k t)

local notation "RT" => rootLane D m p hp contact input site owner align s w G first last P
local notation "row" => SpineRow (r:=P.layers) (m:=m)
private def spineCode (v : Fin (2^n)) :
    row (slotBits v) × Fin p ≃ Fin (∑ j,legWidth v j) :=
  spineBit (r:=P.layers) (m:=m) (p:=p) (slotBits v) (legWidth v) (shape v)
local notation "spine" => spineCode D m p contact input site owner align s w G first last P

private def leftEdge (v : Fin (2^n)) (i : Fin (count H v)) : Boundary splitDevice ⟨v,.inr i⟩ :=
  .inl ⟨.inr ⟨v,i.castSucc⟩,Or.inr (DescentCanonicalRotor.spine_target H v i)⟩
private def rightEdge (v : Fin (2^n)) (i : Fin (count H v)) : Boundary splitDevice ⟨v,.inr i⟩ := .inl ⟨.inr ⟨v,i.succ⟩,Or.inl rfl⟩
local notation "leftAt" => leftEdge D m p contact input site owner align s w G first last P
local notation "rightAt" => rightEdge D m p contact input site owner align s w G first last P

include hp in
def tapLane (v : Fin (2^n)) (i : Fin (count H v)) (back : Bool) (t : row (slotBits v)) : Lane p (widthAt ⟨v,.inr i⟩) :=
  let addr:=fun d : Fin p=>spine v (t,d)
  let law:=spineBit_slope (slotBits v) (legWidth v) (shape v) hp t
  if back then affine hp (leftAt v i) addr (slotBits v t.1) law else affine hp (rightAt v i) addr (slotBits v t.1) law

local notation "tapAt" => tapLane D m p hp contact input site owner align s w G first last P

omit [Fintype R] in
theorem tap_read (a : (DescentPhysicalSplit.graph H).Assignment) (pins : Ports lens) (v : Fin (2^n)) (i : Fin (count H v)) (back : Bool) (t : row (slotBits v)) (d : Fin p) :
    (tapAt v i back t).word (readAt a pins ⟨v,.inr i⟩) d=
      a (.inr ⟨v,if back then i.castSucc else i.succ⟩) (spine v (t,d)) := by
  let addr : Fin p → Fin (∑ j,legWidth v j) := fun d => spine v (t,d)
  have law := spineBit_slope (slotBits v) (legWidth v) (shape v) hp t
  cases back
  · exact congrArg (readAt a pins ⟨v,.inr i⟩) (affine_at (width:=widthAt ⟨v,.inr i⟩)
      hp (rightAt v i) addr (slotBits v t.1) law d)
  · exact congrArg (readAt a pins ⟨v,.inr i⟩) (affine_at (width:=widthAt ⟨v,.inr i⟩)
      hp (leftAt v i) addr (slotBits v t.1) law d)

private def localCode (v : Fin (2^n)) (i : Fin (count H v)) :
    Block P.layers m (slotBits v i) × Fin p ≃ Fin (legWidth v i) :=
  (blockBit P.layers m p (slotBits v i)).trans (finCongr (shape v i).symm)

omit [Fintype C] [Fintype R] [Fintype W] in
private theorem code_eq (v : Fin (2^n)) (i : Fin (count H v)) (t : Block P.layers m (slotBits v i)) (d : Fin p) :
    localCode D m p contact input site owner align s w G first last P v i (t,d) = legDigit D (m*p) G P v i t.1 (finProdFinEquiv (t.2.1,d)) t.2.2 := by
  apply Fin.ext
  change (blockBit P.layers m p (slotBits v i) (t,d)).val = _
  rw [blockBit_val,legDigit_val]; rfl

set_option maxHeartbeats 1000000 in
def program : (q : DescentPhysicalSplit.Vertex H)→DescentLaneGates.Program (2^n) p (widthAt q)
  | ⟨v,.inl false⟩=>{Node:=Fin P.layers × Fin m,op:=fun t=>DescentLaneGates.rotorOp G.arcs C₀ b (P.rotation t.1) v (RT v t.1 t.2)}
  | ⟨_,.inl true⟩=>{Node:=Empty,op:=Empty.elim}
  | ⟨v,.inr i⟩=>{
      Node:=row (slotBits v) ⊕ Block P.layers m (slotBits v i)
      op:=Sum.elim (fun t=>DescentLaneGates.equalOp (.wire (tapAt v i true t)) (.wire (tapAt v i false t)))
        (fun t=>DescentLaneGates.equalOp (.wire (tapAt v i true ⟨i,t⟩)) (outer v i t.1 t.2.1 t.2.2)) }

local notation "prg" => program D m p hp contact input site owner align s w G first last P key
omit [Fintype R] in
/-- The number of batched operations times p equals the number of digitwise operations. -/
theorem node_count_mul (q : DescentPhysicalSplit.Vertex H) : Fintype.card (prg q).Node*p=Fintype.card (legacy q).Node := by
  rcases q with ⟨v,(_|_)|i⟩
  · let rows : (prg ⟨v,.inl false⟩).Node ≃ Fin P.layers × Fin m := Equiv.refl _
    let digitRows : (legacy ⟨v,.inl false⟩).Node ≃ Fin P.layers × Fin (m*p) := Equiv.refl _
    rw [Fintype.card_congr rows,Fintype.card_congr digitRows]
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.mul_assoc]
  · have empty : Fintype.card (prg ⟨v,.inl true⟩).Node = 0 := rfl
    rw [empty,Nat.zero_mul,DescentCanonicalRotor.blank_nodes D (m*p) contact input site owner align s w G first last P key v]
  · let rows : (prg ⟨v,.inr i⟩).Node ≃ row (slotBits v) ⊕ Block P.layers m (slotBits v i) := Equiv.refl _
    have all : Fintype.card (row (slotBits v))*p = ∑ j,legWidth v j := by
      simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (spine v))
    have sel : Fintype.card (Block P.layers m (slotBits v i))*p = legWidth v i := by
      simpa only [Fintype.card_prod,Fintype.card_fin] using
        (Fintype.card_congr (localCode D m p contact input site owner align s w G first last P v i))
    rw [Fintype.card_congr rows,DescentCanonicalRotor.tap_nodes D (m*p) contact input site owner align s w G first last P key v i]
    simp only [Fintype.card_sum,Nat.add_mul]
    rw [all,sel]
    rfl

theorem node_count_mul_le (q : DescentPhysicalSplit.Vertex H) : Fintype.card (prg q).Node*p≤2*DescentNetworkSubstitution.portLoad splitDevice q :=
  (node_count_mul D m p hp contact input site owner align s w G first last P key q).le.trans
    (DescentCanonicalRotor.node_count_le D (m*p) contact input site owner align s w G first last P key q)

private theorem row_count (v : Fin (2^n)) :
    Fintype.card (RowBit G.arcs C₀ b v) = (2+2*h*C₀)*b := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (DescentCanonicalRotor.roster_sum (SlotWidth G.arcs C₀ b v)).trans
    (DescentCanonicalRotor.operand_sum (b:=b) (C₀:=C₀) G v)

set_option maxHeartbeats 1000000 in
omit [Fintype R] in
theorem arity_bound (q : DescentPhysicalSplit.Vertex H) (z : (prg q).Node) : ((prg q).op z).arity≤ max 2 ((2+2*h*C₀)*b) := by
  rcases q with ⟨v,(_|_)|i⟩
  · exact (row_count (C₀:=C₀) (b:=b) G v).le.trans (Nat.le_max_right _ _)
  · exact z.elim
  · rcases z with t|t
    · exact (equal_arity (Y:=2^n) (.wire (tapAt v i true t)) (.wire (tapAt v i false t))).trans (Nat.le_max_left _ _)
    · exact (equal_arity (Y:=2^n) (.wire (tapAt v i true ⟨i,t⟩)) (outer v i t.1 t.2.1 t.2.2)).trans
        (Nat.le_max_left _ _)

omit [Fintype R] in
private theorem tapStride (v : Fin (2^n)) (i : Fin (count H v)) (back : Bool) (t : row (slotBits v)) :
    (tapAt v i back t).stride ≤ max 1 (max b (C₀*b)) := by
  cases back <;> exact (tapBits_le D (m*p) G P v t.1).trans (Nat.le_max_right _ _)

omit [Fintype R] in
theorem stride_bound (q : DescentPhysicalSplit.Vertex H) (z : (prg q).Node) (j : Fin ((prg q).op z).arity) :
    (((prg q).op z).arg j).stride ≤ max 1 (max b (C₀*b)) := by
  rcases q with ⟨v,(_|_)|i⟩
  · let t : RowBit G.arcs C₀ b v:=(rowSerial G.arcs C₀ b v).symm j
    change SlotWidth G.arcs C₀ b v t.1≤_
    rcases t with ⟨z|z,t⟩
    · exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    · exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  · exact z.elim
  · rcases z with t|t
    · refine equal_stride (Y:=2^n) (.wire (tapAt v i true t)) (.wire (tapAt v i false t)) _ ?_ ?_ j
      · rintro l h;cases h;exact tapStride D m p hp contact input site owner align s w G first last P v i true t
      · rintro l h;cases h;exact tapStride D m p hp contact input site owner align s w G first last P v i false t
    · refine equal_stride (Y:=2^n) (.wire (tapAt v i true ⟨i,t⟩)) (outer v i t.1 t.2.1 t.2.2) _ ?_ ?_ j
      · rintro l h;cases h;exact tapStride D m p hp contact input site owner align s w G first last P v i true ⟨i,t⟩
      · exact tapLegLane_stride D (m*p) contact input site owner align s w G first last P key rfl hp v i t.1 t.2.1 t.2.2

variable (menu : ∀π,Configures K G.arcs C₀ b π)
local notation "romWord" => rom G.arcs C₀ b (fixedTable menu)
local notation "evalAt" => DescentLaneGates.scalar G.arcs C₀ b p romWord

set_option maxHeartbeats 1800000 in
omit [Fintype R] in
theorem program_read (a : (DescentPhysicalSplit.graph H).Assignment) (pins : Ports lens)
    (q : DescentPhysicalSplit.Vertex H) :
    (prg q).recipe.value evalAt (readAt a pins q) = (A).read T a pins q := by
  have adapter : (A).read T a pins q =
      (Physical.rotor G P D).read (Physical.rotorTables G P D) a (pinsAt pins) q :=
    DescentLocalAdapters.read (Physical.rotor G P D) positionAt lens (Physical.rotorTables G P D) pinsAt
      (DescentGoodRouter.Ordered.local_pins D (m*p) contact input site owner align s w G first last P key) a pins q
  refine (DescentLaneGates.Program.read (prg q) evalAt (readAt a pins q)).trans (Eq.trans ?_ adapter.symm)
  rcases q with ⟨v,(_|_)|i⟩
  · refine Eq.trans ?_ ((rotor_correct G P D menu) a (pinsAt pins) ⟨v,.inl false⟩).symm
    let x := a (.inr ⟨v,0⟩)
    let price (r : Fin P.layers) (j : Fin (m*p)) := romWord (rootAddress G P D v (tuple H v x) r j)
    let chunk (t : Fin P.layers × Fin m) := ∏ d : Fin p, price t.1 (finProdFinEquiv (t.2,d))
    have requests (t : Fin P.layers × Fin m) :
        ((prg ⟨v,.inl false⟩).op t).value evalAt (readAt a pins ⟨v,.inl false⟩) = chunk t := by
      refine (DescentLaneGates.rotor_read G.arcs C₀ b romWord (P.rotation t.1) v
        (RT v t.1 t.2) (readAt a pins ⟨v,.inl false⟩)).trans ?_
      apply Finset.prod_congr rfl
      intro d _
      let k : Fin (m*p) := finProdFinEquiv (t.2,d)
      let cols (z : Slot G.arcs v) (j : Fin (SlotWidth G.arcs C₀ b v z)) :=
        (RT v t.1 t.2 ⟨z,j⟩).word (readAt a pins ⟨v,.inl false⟩) d
      have readCols : cols = (fun z j => x (rootColumn G P D v t.1 k z j)) := by
        funext z j
        let port : Boundary splitDevice ⟨v,.inl false⟩ := .inl ⟨.inr ⟨v,0⟩,Or.inl rfl⟩
        let bits (digit : Fin p) : Fin (widthAt ⟨v,.inl false⟩ port) :=
          rootColumn G P D v t.1 (finProdFinEquiv (t.2,digit)) z j
        exact congrArg (readAt a pins ⟨v,.inl false⟩)
          (DescentLaneGates.affine_at (width:=widthAt ⟨v,.inl false⟩) hp port bits
            (SlotWidth G.arcs C₀ b v z)
            (root_slope D m p hp contact input site owner align s w G first last P v t.1 t.2 ⟨z,j⟩) d)
      exact (congrArg (fun f => romWord (rootKey G P v t.1 f)) readCols).trans
        (congrArg romWord (rootKey_read G P D v t.1 k x))
    let rows : (prg ⟨v,.inl false⟩).Node ≃ Fin P.layers × Fin m := Equiv.refl _
    refine (Fintype.prod_equiv rows _ chunk (fun t => requests (rows t))).trans ?_
    change (∏ t : Fin P.layers × Fin m, chunk t) = ∏ t : Fin P.layers × Fin (m*p), price t.1 t.2
    refine (Fintype.prod_prod_type chunk).trans (Eq.trans ?_
      (Fintype.prod_prod_type (fun t : Fin P.layers × Fin (m*p) => price t.1 t.2)).symm)
    apply Finset.prod_congr rfl
    intro r _
    exact (Fintype.prod_prod_type (fun kd : Fin m × Fin p => price r (finProdFinEquiv kd))).symm.trans
      (finProdFinEquiv.prod_comp (price r))
  · refine Eq.trans ?_ (DescentPhysicalSplit.read_eq H (Physical.hostTables G.arcs P.tables) a (pinsAt pins)
      ⟨v,.inl true⟩).symm
    change (∏ j : Empty, ((prg ⟨v,.inl true⟩).op j).value evalAt (readAt a pins ⟨v,.inl true⟩)) = 1
    simp
  · refine Eq.trans ?_ (DescentPhysicalSplit.read_eq H (Physical.hostTables G.arcs P.tables) a (pinsAt pins)
      ⟨v,.inr i⟩).symm
    let left := a (.inr ⟨v,i.castSucc⟩)
    let right := a (.inr ⟨v,i.succ⟩)
    let x := args H (decode H a).1 (pinsAt pins) v i
    let addr := localCode D m p contact input site owner align s w G first last P v i
    let rd := readAt a pins ⟨v,.inr i⟩
    let pred : (row (slotBits v) ⊕ Block P.layers m (slotBits v i)) → Prop := Sum.elim
      (fun t => ∀ d, left (spine v (t,d)) = right (spine v (t,d)))
      (fun t => ∀ d, left (spine v (⟨i,t⟩,d)) = x (addr (t,d)))
    have leftWord (t : row (slotBits v)) :
        (tapAt v i true t).word rd = fun d => left (spine v (t,d)) := by
      funext d
      exact tap_read D m p hp contact input site owner align s w G first last P a pins v i true t d
    have rightWord (t : row (slotBits v)) :
        (tapAt v i false t).word rd = fun d => right (spine v (t,d)) := by
      funext d
      exact tap_read D m p hp contact input site owner align s w G first last P a pins v i false t d
    have selected (t : Block P.layers m (slotBits v i)) :
        (outer v i t.1 t.2.1 t.2.2).read rd = fun d => x (addr (t,d)) := by
      funext d
      exact (tapLegLane_read D (m*p) contact input site owner align s w G first last P key rfl hp a pins
        v i t.1 t.2.1 t.2.2 d).trans (congrArg x
          (code_eq D m p contact input site owner align s w G first last P v i t d).symm)
    have test (t : row (slotBits v) ⊕ Block P.layers m (slotBits v i)) :
        ((prg ⟨v,.inr i⟩).op t).value evalAt rd = if pred t then 1 else 0 := by
      rcases t with t|t
      · refine (DescentLaneGates.equal_read G.arcs C₀ b romWord hp
          (.wire (tapAt v i true t)) (.wire (tapAt v i false t)) rd).trans
          (DescentCanonicalRotor.equal_test (1:K) 0 ?_)
        change ((tapAt v i true t).word rd = (tapAt v i false t).word rd) ↔
          ∀ d, left (spine v (t,d)) = right (spine v (t,d))
        rw [leftWord t,rightWord t]
        exact ⟨fun e d => congrFun e d,fun e => funext e⟩
      · refine (DescentLaneGates.equal_read G.arcs C₀ b romWord hp
          (.wire (tapAt v i true ⟨i,t⟩)) (outer v i t.1 t.2.1 t.2.2) rd).trans
          (DescentCanonicalRotor.equal_test (1:K) 0 ?_)
        change ((tapAt v i true ⟨i,t⟩).word rd = (outer v i t.1 t.2.1 t.2.2).read rd) ↔
          ∀ d, left (spine v (⟨i,t⟩,d)) = x (addr (t,d))
        rw [leftWord ⟨i,t⟩,selected t]
        exact ⟨fun e d => congrFun e d,fun e => funext e⟩
    let rows : (prg ⟨v,.inr i⟩).Node ≃ row (slotBits v) ⊕ Block P.layers m (slotBits v i) := Equiv.refl _
    refine (Fintype.prod_equiv rows _ (fun t => if pred t then (1 : K) else 0)
      (fun t => test (rows t))).trans ((product_checks (K:=K) pred).trans ?_)
    have law : (∀ t, pred t) ↔ tuple H v left = tuple H v right ∧ tuple H v left i = x := by
      constructor
      · intro all
        constructor
        · apply congrArg (tuple H v)
          funext j
          obtain ⟨⟨t,d⟩,rfl⟩ := (spine v).surjective j
          exact all (.inl t) d
        · funext j
          obtain ⟨⟨t,d⟩,rfl⟩ := addr.surjective j
          exact all (.inr t) d
      · rintro ⟨same,sel⟩ (t|t) d
        · exact congrFun ((tuple H v).injective same) (spine v (t,d))
        · exact congrFun sel (addr (t,d))
    exact DescentCanonicalRotor.equal_test (1:K) 0 law

end
end Hierarchy.DescentBatchedRotor

end OAI
