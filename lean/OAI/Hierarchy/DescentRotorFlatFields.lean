import OAI.Hierarchy.DescentRotorMixedQuery
import OAI.Hierarchy.DescentResetLaneIssue
import OAI.Hierarchy.DescentBundleLanes

namespace OAI
/-! # Private rotor operands in the flattened list of addressed payload words -/
namespace Hierarchy.DescentRotorOperandQueryROM.Shape
open DescentSIMDLookup DescentPackedZip DescentDenseHostOrder DescentResetHostSize DescentHostDirectory
open DescentPhysicalSplit DescentBatchedNodeOrder DescentRotor DescentLaneGates DescentCommonHost DescentResetLaneIssue
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open private cablePort from OAI.Hierarchy.DescentPhysicalSplit
open private Physical.endpoint from OAI.Hierarchy.DescentRotorNetwork
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h) (C : Shape)
local notation "Q" => DescentCommonPalette.rotor board
local notation "H₀" => Physical.host board.arcs 0 0 0 0 0
local notation "P" => ↥(roster board C.residual C.depth)

structure PrivateLane where
  face : Bool
  edge : (Q).Edge
  address : ℕ
  start : ℕ
  stride : ℕ

def PrivateLane.units (mult layers : ℕ) (l : PrivateLane board) :=
  layers*(C.batches*DescentRotorPrivateFields.price board mult C.packet l.edge)
def PrivateLane.count (mult layers grain : ℕ) (l : PrivateLane board) :=
  min (l.stride+1) (l.units board C mult layers-l.start/grain)
def PrivateLane.names (mult layers grain : ℕ) (l : PrivateLane board) :=
  List.ofFn fun z : Fin (l.count board C mult layers grain)=>(l,z.val)

/-- The finite local index read by an actual scalar root port. -/
def staticRootSlot (v : Fin (2^n)) : Slot board.arcs v→Fin (DescentPhysicalSplit.count H₀ v)
  | .inl side=>DescentPhysicalSplit.index H₀ v ⟨.inl (v,side),rfl⟩
  | .inr q=>DescentPhysicalSplit.index H₀ v (cablePort H₀ v (Physical.endpoint board.arcs v q))

def rootReference (mult layers grain : ℕ) (v : Fin (2^n)) (t : RowBit board.arcs mult C.packet v)
    (r : Fin layers) (b : Fin C.batches) : PrivateLane board :=
  let step:=SlotWidth board.arcs mult C.packet v t.1
  let before:=portPrefix (C.subrow board mult v) (staticRootSlot board v t.1)
  ⟨false,.inr ⟨v,0⟩,r.val*C.batches+b.val,start C.batches grain before step t.2.val layers r.val b.val,step⟩

def spineReference (mult layers grain : ℕ) (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count H₀ v)) (before : Bool)
    (t : SpineRow (r:=layers) (m:=C.batches) (C.subrow board mult v)) : PrivateLane board :=
  let step:=C.subrow board mult v t.1
  ⟨before,.inr ⟨v,if before then i.castSucc else i.succ⟩,t.2.1.val*C.batches+t.2.2.1.val,
   start C.batches grain (portPrefix (C.subrow board mult v) t.1) step t.2.2.2.val layers t.2.1.val t.2.2.1.val,step⟩

def supplyReference (mult layers grain : ℕ) (e : (H₀).Edge) (dir : Bool) (r : Fin layers) (b : Fin C.batches)
    (bit : ℕ) : PrivateLane board :=
  ⟨dir,.inl e,r.val*C.batches+b.val,start C.batches grain 0 (mult*C.packet) bit layers r.val b.val,mult*C.packet⟩

/-- Private references in formal-argument order. At a selected public tap the final operand
belongs to the separate public family, and all private formal arguments precede it. -/
def privateRows (mult layers grain node : ℕ) : (Q).Site→List (PrivateLane board)
  | ⟨v,.inl false⟩=>
    if live : node<layers*C.batches then
      let rb : Fin layers×Fin C.batches:=finProdFinEquiv.symm ⟨node,live⟩
      List.ofFn fun a=>C.rootReference board mult layers grain v ((rowSerial board.arcs mult C.packet v).symm a) rb.1 rb.2
    else []
  | ⟨_,.inl true⟩=>[]
  | ⟨v,.inr i⟩=>
    let order:=tapOrder layers C.batches (C.subrow board mult v) i
    if live : node<Fintype.card (SpineRow (r:=layers) (m:=C.batches) (C.subrow board mult v) ⊕
        Block layers C.batches (C.subrow board mult v i)) then
      match order.symm ⟨node,live⟩ with
      | .inl t=>[C.spineReference board mult layers grain v i true t,C.spineReference board mult layers grain v i false t]
      | .inr t=>
        let back:=C.spineReference board mult layers grain v i true ⟨i,t⟩
        match name H₀ v i with
        | .inl _=>[back]
        | .inr (e,dir)=>[back,C.supplyReference board mult layers grain e dir t.1 t.2.1 t.2.2.val]
    else []

def flattened (mult layers grain node : ℕ) (v : (Q).Site) :=
  (C.privateRows board mult layers grain node v).flatMap (PrivateLane.names board C mult layers grain)

def PrivateLane.kept (mult layers grain split stepWithin : ℕ) (l : PrivateLane board) (f : Fin 7) : ℕ :=
  let word:=l.start/grain+stepWithin
  ![0,0,word/split,word%split,l.start%grain,l.stride,l.count board C mult layers grain] f

/-- Query and retained correction, all keyed by the identical flattened (node,argument)
coordinate. Field zero selects the query; fields one through seven select the retained part. -/
def flatReg (mult grain split node arg : ℕ) (f : Fin 8) (x : Fin 4→Cell C.fieldBits) : ℕ :=
  if active : (x 1).val>0 ∧ (x 2).val%2=0 ∧ (x 3).val<(roster board C.residual C.depth).card then
    match ((DescentResetTrunkPalette.order board C.residual C.depth).symm ⟨(x 3).val,active.2.2⟩).val with
    | .good side z v=>
      let root:=((x 1).val-1,z.2)
      if allowed : root∈codes C.residual then
        let levels:=DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val
        match (C.flattened board mult levels grain node v)[arg]? with
        | some (l,within)=>if bounded : l.address<C.addresses then
            Fin.cases ((C.value board (side,l.face,⟨root,allowed⟩,l.edge,⟨l.address,bounded⟩) (C.registers x)).val)
              (l.kept board C mult levels grain split within) f else 0
        | none=>0
      else 0
    | _=>0
  else 0

def flatFamily (mult grain split slots nodes bits : ℕ) (j : Fin (8*(slots*nodes))) (x : Fin 4→Cell C.fieldBits) : Cell bits :=
  let (f,z):=finProdFinEquiv.symm j
  let (a,i):=(finProdFinEquiv.symm z : Fin slots×Fin nodes)
  C.flatReg board mult grain split i.val a.val f x

theorem flat_issued {H G w : ℕ} (mult grain split slots nodes bits base : ℕ)
    (field : Fin 8) (arg : Fin slots) (node : Fin nodes) (old : Fin 4→Expr) (mem : Memory w)
    (x : Fin H→Fin G→Fin 4→Cell C.fieldBits) (held : ∀i,(old i).Fits w base)
    (prior : ∀i,Source (old i) (fun v g=>x v g i) C.lanes mem)
    (room : DescentOperandFamilyBook.endAddress (8*(slots*nodes)) 4 C.fieldBits C.lanes base<2^w) :
    let idx:=finProdFinEquiv (field,finProdFinEquiv (arg,node))
    let F:=C.flatFamily board mult grain split slots nodes bits
    let op:=DescentOperandFamilyBook.expr F C.lanes base idx old
    op.Fits w (DescentOperandFamilyBook.endAddress (8*(slots*nodes)) 4 C.fieldBits C.lanes base) ∧
    Source op (fun v g=>(C.flatReg board mult grain split node.val arg.val field (x v g):Cell bits)) C.lanes
      (DescentOperandFamilyBook.image F C.lanes base mem) := by
  intro idx F op
  have empty (j) : F j (fun _=>0)=0:=by simp [F,flatFamily,flatReg]
  simpa only [op,F,idx,flatFamily,Equiv.symm_apply_apply] using
    DescentOperandFamilyBook.issued F empty C.lanes base idx old mem x held prior room

theorem flat_at (mult grain split node arg : ℕ) (x : Fin 4→Cell C.fieldBits) (s : Bool)
    (key : Code C.residual) (v : (Q).Site) (shape : P) (l : PrivateLane board) (within : ℕ)
    (depth : (x 1).val=key.val.1+1) (safe : (x 2).val%2=0) (seen : (x 3).val=(localRank board C.residual C.depth shape).val)
    (good : shape.val=.good s ((),key.val.2) v)
    (fetch : (C.flattened board mult (DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val) grain node v)[arg]?=some (l,within))
    (bound : l.address<C.addresses) :
    C.flatReg board mult grain split node arg 0 x=
      (C.value board (s,l.face,key,l.edge,⟨l.address,bound⟩) (C.registers x)).val ∧
    ∀f : Fin 7,C.flatReg board mult grain split node arg f.succ x=
       l.kept board C mult (DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val) grain split within f := by
  have real : (x 3).val<(roster board C.residual C.depth).card:=seen ▸ (localRank board C.residual C.depth shape).isLt
  have known : (⟨(x 3).val,real⟩ : Fin (roster board C.residual C.depth).card)=
    DescentResetTrunkPalette.order board C.residual C.depth shape:=Fin.ext seen
  have active : 0<key.val.1+1 ∧ (x 2).val%2=0 ∧ (x 3).val<(roster board C.residual C.depth).card :=
    ⟨Nat.zero_lt_succ _,safe,real⟩
  simp only [flatReg,depth,dite_eq_left active,known,Equiv.symm_apply_apply,good,
    Nat.add_sub_cancel,Prod.mk.eta,key.property,dite_eq_left,fetch,bound,Fin.cases_zero,Fin.cases_succ,true_and,implies_true]

end
end Hierarchy.DescentRotorOperandQueryROM.Shape

end OAI
