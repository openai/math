import OAI.Hierarchy.DescentRotorFlatFields
import OAI.Hierarchy.DescentBundleTerminal

namespace OAI
/-! # Readback of flattened private rotor words on their actual circuit operands -/
namespace Hierarchy.DescentRotorOperandQueryROM.Shape
open DescentSIMDLookup DescentPhysicalSplit DescentBatchedNodeOrder DescentRotor DescentLaneGates DescentCommonHost
open DescentBatchedRotor DescentResetGates DescentRouterSlots DescentKernelHistory DescentBundleHistory
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 2500000
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h) (C : Shape)
local notation "Q" => DescentCommonPalette.rotor G
local notation "H₀" => Physical.host G.arcs 0 0 0 0 0

theorem privateUnits_width (D levels mult p : ℕ) (hp : 0<p) (l : PrivateLane G) :
    ((graph (Physical.host G.arcs D levels mult C.packet (C.batches*p))).width
      (DescentCommonPalette.rotorEdge G D levels mult C.packet (C.batches*p) l.edge))/p=
      l.units G C mult levels := by
  rw [DescentRotorPrivateFields.edge_width]
  rw [show levels*(C.batches*p*DescentRotorPrivateFields.price G mult C.packet l.edge)=
      l.units G C mult levels*p by dsimp [PrivateLane.units];ring,Nat.mul_div_cancel _ hp]

theorem root_rows (mult layers p : ℕ) (v : Fin (2^n)) (r : Fin layers) (b : Fin C.batches) :
    C.privateRows G mult layers p (finProdFinEquiv (r,b)).val ⟨v,.inl false⟩=
      List.ofFn (fun a=>C.rootReference G mult layers p v ((rowSerial G.arcs mult C.packet v).symm a) r b) := by
  simp only [privateRows, dite_eq_left (finProdFinEquiv (r,b)).isLt, Fin.eta, Equiv.symm_apply_apply]
theorem spine_rows (mult layers p : ℕ) (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count H₀ v))
    (t : SpineRow (r:=layers) (m:=C.batches) (C.subrow G mult v)) :
    C.privateRows G mult layers p (tapOrder layers C.batches (C.subrow G mult v) i (.inl t)).val ⟨v,.inr i⟩=
      [C.spineReference G mult layers p v i true t,C.spineReference G mult layers p v i false t] := by
  simp only [privateRows, dite_eq_left ((tapOrder layers C.batches (C.subrow G mult v) i) (.inl t)).isLt, Fin.eta, Equiv.symm_apply_apply]
theorem selected_rows (mult layers p : ℕ) (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count H₀ v))
    (t : Block layers C.batches (C.subrow G mult v i)) :
    C.privateRows G mult layers p (tapOrder layers C.batches (C.subrow G mult v) i (.inr t)).val ⟨v,.inr i⟩=
      let back:=C.spineReference G mult layers p v i true ⟨i,t⟩
      match name H₀ v i with
      | .inl _=>[back]
      | .inr (e,dir)=>[back,C.supplyReference G mult layers p e dir t.1 t.2.1 t.2.2.val] := by
  simp only [privateRows, dite_eq_left ((tapOrder layers C.batches (C.subrow G mult v) i) (.inr t)).isLt, Fin.eta, Equiv.symm_apply_apply]
  cases name H₀ v i with
  | inl _ => rfl
  | inr t => rcases t with ⟨e,dir⟩; rfl

theorem flatten_member (mult layers p node : ℕ) (site : (Q).Site) (l : PrivateLane G)
    (left right : List (PrivateLane G)) (atRow : C.privateRows G mult layers p node site=left++l::right)
    (j : Fin (l.count G C mult layers p)) :
    (C.flattened G mult layers p node site)[(left.flatMap (PrivateLane.names G C mult layers p)).length+j.val]?=some (l,j.val) := by
  rw [flattened,atRow,List.flatMap_append,List.flatMap_cons,List.getElem?_append_right (Nat.le_add_right ..),
    Nat.add_sub_cancel_left,List.getElem?_append_left (by simp [PrivateLane.names])]
  simp [PrivateLane.names]

/-- Each p-word named by the recorded strided operand has this literal cable block number.
All words in the same lane have the same decoded span. -/
theorem physical_span {A : Type} {width : A→ℕ} {p : ℕ} (hp : 0<p) (mult levels split : ℕ)
    (q : PrivateLane G) (l : Lane p width) (units : A→ℕ) (multiple : ∀a,width a=units a*p)
    (sameStart : l.start=q.start) (sameStride : l.stride=q.stride) (size : units l.port=q.units G C mult levels)
    (j : Fin (l.count units)) :
    let s:=laneSlice (hw:=fun _ : Empty=>0) units multiple hp l
    let z:=q.kept G C mult levels p split j.val
    z 4=s.start ∧ z 5=s.stride ∧ z 6=s.count ∧
      (s.get j).elim (fun a=>z 2=a.block/split ∧ z 3=a.block%split) (fun a=>a.port.elim) := by
  refine ⟨?_,?_,?_,?_⟩
  · change q.start%p=l.start%p;rw [sameStart]
  · exact sameStride.symm
  · change min (q.stride+1) (q.units G C mult levels-q.start/p)=min (l.stride+1) (units l.port-l.start/p)
    rw [sameStart,sameStride,size]
  · change (q.start/p+j.val)/split=(l.start/p+j.val)/split ∧
      (q.start/p+j.val)%split=(l.start/p+j.val)%split
    simp [sameStart]

open DescentCommonPalette DescentResetLaneIssue
section RowTransports

variable {E K : Type} [Fintype E] [Field K] {hostUnits mult : ℕ}
variable {hw : 0<C.packet} {pay : ℝ} {src dst : E→Fin (2^n)}

def bareSlot (D levels mult hostUnits : ℕ) (v : Fin (2^n))
    (i : Fin (DescentPhysicalSplit.count (Physical.host G.arcs D levels mult C.packet hostUnits) v)) :
    Fin (DescentPhysicalSplit.count H₀ v) :=
  Fin.cast (rotor_count_eq G D levels mult C.packet hostUnits v).symm i

private theorem tapBits_cast (D : ℕ)
    (P : BaseCircuit K G mult C.packet hostUnits hw src dst pay) (v : Fin (2^n))
    (i : Fin (DescentPhysicalSplit.count H₀ v)) :
    tapBits D hostUnits G P v (Fin.cast (rotor_count_eq G D P.layers mult C.packet hostUnits v) i) =
      C.subrow G mult v i := by
  unfold tapBits subrow
  rw [rotor_name_cast G D P.layers mult C.packet hostUnits v i]
  cases name H₀ v i <;> rfl

private theorem prefix_cast {a b : ℕ} (eqn : a=b) (physical : Fin b→ℕ) (bare : Fin a→ℕ)
    (same : ∀ i,physical (Fin.cast eqn i)=bare i) (j : Fin a) :
    portPrefix physical (Fin.cast eqn j)=portPrefix bare j := by
  subst b
  have funcs : physical=bare := funext same
  cases funcs
  rfl

theorem tapPrefix_cast (D : ℕ) (P : BaseCircuit K G mult C.packet hostUnits hw src dst pay)
    (v : Fin (2^n)) (j : Fin (DescentPhysicalSplit.count H₀ v)) :
    portPrefix (tapBits D hostUnits G P v)
        (Fin.cast (rotor_count_eq G D P.layers mult C.packet hostUnits v) j) =
      portPrefix (C.subrow G mult v) j :=
  prefix_cast _ _ _ (tapBits_cast G C D P v) j

theorem tapBits_bare (D : ℕ) (P : BaseCircuit K G mult C.packet hostUnits hw src dst pay)
    (v : Fin (2^n))
    (i : Fin (DescentPhysicalSplit.count (Physical.host G.arcs D P.layers mult C.packet hostUnits) v)) :
    tapBits D hostUnits G P v i=C.subrow G mult v (bareSlot G C D P.layers mult hostUnits v i) := by
  have eqn : Fin.cast (rotor_count_eq G D P.layers mult C.packet hostUnits v)
      (bareSlot G C D P.layers mult hostUnits v i)=i := Fin.ext rfl
  have words:=tapBits_cast G C D P v (bareSlot G C D P.layers mult hostUnits v i)
  rw [eqn] at words
  exact words

theorem tapPrefix_bare (D : ℕ) (P : BaseCircuit K G mult C.packet hostUnits hw src dst pay)
    (v : Fin (2^n))
    (i : Fin (DescentPhysicalSplit.count (Physical.host G.arcs D P.layers mult C.packet hostUnits) v)) :
    portPrefix (tapBits D hostUnits G P v) i=
      portPrefix (C.subrow G mult v) (bareSlot G C D P.layers mult hostUnits v i) := by
  have eqn : Fin.cast (rotor_count_eq G D P.layers mult C.packet hostUnits v)
      (bareSlot G C D P.layers mult hostUnits v i)=i := Fin.ext rfl
  have words:=tapPrefix_cast G C D P v (bareSlot G C D P.layers mult hostUnits v i)
  rw [eqn] at words
  exact words

def bareSpineRow (D : ℕ) (P : BaseCircuit K G mult C.packet hostUnits hw src dst pay)
    (v : Fin (2^n)) (t : SpineRow (r:=P.layers) (m:=C.batches) (tapBits D hostUnits G P v)) :
    SpineRow (r:=P.layers) (m:=C.batches) (C.subrow G mult v) :=
  ⟨bareSlot G C D P.layers mult hostUnits v t.1,
    t.2.1,t.2.2.1,Fin.cast (tapBits_bare G C D P v t.1) t.2.2.2⟩

private theorem spineEnd_cast {a b : ℕ} (eqn : a=b) (j : Fin b) (back : Bool) :
    Fin.cast (congrArg (fun k : ℕ=>k+1) eqn)
      (if back then (Fin.cast eqn.symm j).castSucc else (Fin.cast eqn.symm j).succ) =
      (if back then j.castSucc else j.succ) := by
  subst b
  cases back <;> rfl

private theorem rootZero_cast {a b : ℕ} (eqn : a=b) :
    Fin.cast (congrArg (fun k : ℕ=>k+1) eqn) (0 : Fin (a+1))=0 := Fin.ext (by simp)

end RowTransports

section Physical
variable {I U R W K : Type} [Fintype I] [Fintype U] [Fintype R] [Fintype W] [Field K]
variable (D p : ℕ) (hp : 0<p) (contact : I→U) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→U→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {mult num : ℕ}
variable {hw : 0<C.packet} {pay : ℝ} (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
local notation "u" => C.batches*p
variable (P : BaseCircuit K G mult C.packet (C.batches*p) hw
  (fun e : Item contact owner s w => first (root contact input site owner s w align e))
  (fun e : Item contact owner s w => last (link contact owner s w e)) pay) (key : I↪Fin num)
local notation "H" => Physical.host G.arcs D P.layers mult C.packet u
local notation "prg" => DescentBatchedRotor.program D C.batches p hp contact input site owner align s w G first last P key
local notation "tap" => tapLane D C.batches p hp contact input site owner align s w G first last P

open private cablePort from OAI.Hierarchy.DescentPhysicalSplit
open private Physical.endpoint from OAI.Hierarchy.DescentRotorNetwork

omit [Fintype U] [Fintype R] [Fintype W] in
private theorem rootHostSlot_cast (v : Fin (2^n)) (side : Slot G.arcs v) :
    Fin.cast (DescentCommonPalette.rotor_count_eq G D P.layers mult C.packet u v)
      (staticRootSlot G v side) =
      DescentResetLaneIssue.rootHostSlot D C.batches p contact input site owner align s w G first last P v side := by
  symm
  cases side with
  | inl bit =>
    exact DescentCommonPalette.rotor_index_cast G D P.layers mult C.packet u v
      ⟨.inl (v,bit),rfl⟩ ⟨.inl (v,bit),rfl⟩ rfl
  | inr q =>
    let e := Physical.endpoint G.arcs v q
    apply DescentCommonPalette.rotor_index_cast G D P.layers mult C.packet u v
      (cablePort H₀ v e) (cablePort H v e)
    by_cases h₀ : (H₀).src e.val=v
    · have h₁ : (H).src e.val=v := h₀
      simp only [cablePort, dite_eq_left h₀, dite_eq_left h₁]
      rfl
    · have h₁ : ¬(H).src e.val=v := h₀
      simp only [cablePort, dite_eq_right h₀, dite_eq_right h₁]
      rfl

omit [Fintype R] in
theorem root_reference_read (v : Fin (2^n)) (r : Fin P.layers) (b : Fin C.batches)
    (t : RowBit G.arcs mult C.packet v) :
    let l:=((prg ⟨v,.inl false⟩).op (r,b)).arg (rowSerial G.arcs mult C.packet v t)
    let req:=C.rootReference G mult P.layers p v t r b
    (Sum.map Subtype.val Subtype.val l.port,l.start,l.stride)=
      (.inl (rotorEdge G D P.layers mult C.packet u req.edge),req.start,req.stride) := by
  dsimp only
  refine (DescentResetLaneIssue.root_fields D C.batches p hp contact input site owner align s w G first last P key v r b t).trans ?_
  have eqn:=rootHostSlot_cast G C D p contact input site owner align s w first last P v t.1
  have before:=tapPrefix_cast G C D P v (staticRootSlot G v t.1)
  rw [eqn] at before
  simp only [rootReference,rotorEdge_spine,before]
  rw [rootZero_cast (rotor_count_eq G D P.layers mult C.packet u v)]

omit [Fintype R] in
theorem spine_reference_read (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count H v))
    (back : Bool) (t : SpineRow (r:=P.layers) (m:=C.batches) (tapBits D u G P v)) :
    let l:=tap v i back t
    let req:=C.spineReference G mult P.layers p v (bareSlot G C D P.layers mult u v i) back
      (bareSpineRow G C D P v t)
    (Sum.map Subtype.val Subtype.val l.port,l.start,l.stride)=
      (.inl (rotorEdge G D P.layers mult C.packet u req.edge),req.start,req.stride) := by
  dsimp only
  refine (DescentResetLaneIssue.tap_fields D C.batches p hp contact input site owner align s w G first last P v i back t).trans ?_
  have endEq := spineEnd_cast (rotor_count_eq G D P.layers mult C.packet u v) i back
  change Fin.cast _ (if back then (bareSlot G C D P.layers mult u v i).castSucc
      else (bareSlot G C D P.layers mult u v i).succ) = _ at endEq
  simp only [spineReference,bareSpineRow,Fin.val_cast,rotorEdge_spine,endEq,
    tapPrefix_bare G C D P v t.1,tapBits_bare G C D P v t.1]

omit [Fintype R] in
theorem supply_reference_read (e : (H).Edge) (dir : Bool) (r : Fin P.layers) (b : Fin C.batches) (j : Fin (mult*C.packet)) :
    let l:=legLane D u contact input site owner align s w G first last P key (m:=C.batches) (p:=p) rfl hp (.inr (e,dir)) r b j
    let req:=C.supplyReference G mult P.layers p e dir r b j.val
    (match l with
     | .fixed _=>none
     | .wire l'=>some (Sum.map Subtype.val Subtype.val l'.port,l'.start,l'.stride))=some (.inl (rotorEdge G D P.layers mult C.packet u req.edge),req.start,req.stride)  := by
  have seen := DescentResetLaneIssue.private_supply_fields D C.batches p hp contact input site owner align s w G first last P key e dir r b j
  dsimp only at seen ⊢
  cases h : legLane D u contact input site owner align s w G first last P key (m:=C.batches) (p:=p) rfl hp (.inr (e,dir)) r b j <;> rw [h] at seen <;> exact seen

end Physical
end
end Hierarchy.DescentRotorOperandQueryROM.Shape

end OAI
