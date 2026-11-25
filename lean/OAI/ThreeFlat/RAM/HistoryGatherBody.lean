import OAI.ThreeFlat.RAM.HistoryGatherGeometry
import OAI.ThreeFlat.Diagonal.ShrinkDemandCD
import OAI.ThreeFlat.RAM.HistoryScopeReaders
import OAI.ThreeFlat.Diagonal.RefreshPartyWidthNative
import OAI.ThreeFlat.RAM.WordQuotients
import OAI.ThreeFlat.RAM.HistoryPartyPair
import OAI.ThreeFlat.RAM.HistoryNodePorts
import OAI.ThreeFlat.RAM.HistoryPortCatalogue
import OAI.ThreeFlat.Diagonal.RefreshPartyWidth

namespace OAI
/-! # Emitting the true old and new address of every bit of a selected party -/

namespace ThreeFlat.RAM.HistoryGatherBody

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM DescriptorExpr PhysicalProcedure PhysicalPinsExpr
open HistoryPartyBatch
open Diagonal.CompressorPacking.Native
open scoped Fin.CommRing Classical

noncomputable section
variable {W : ℕ}

structure Layout where
  party : HistoryPartyBatch.Layout
  nodePorts : HistoryNodePorts.Layout
  mode : Geometry
  histogramStride : ℕ
  temp : ℕ
  demandCap : ℕ
  supplyCap : ℕ
  digitCap : ℕ
  catalogue : ℕ
  privateStarts : ℕ

private abbrev T (W : ℕ) := Term W 0 1
private def l (x : ℕ) : T W := .literal (x : Word W)
private def a (x y : T W) : T W := .binary .add x y
private def times (x y : T W) : T W := .binary .mul x y
private def read (x : T W) (j : ℕ) : T W := (a x (l j)).load
private def minus (x y : T W) : T W := .select .lt x y (l 0) (.binary .sub x y)
private def choice (idx : T W) : ℕ → List (T W) → T W
  | _,[] => l 0
  | i,t::ts => .select .eq idx (l i) t (choice idx (i+1) ts)

private def nF (e : Formula 1) : T W := HeaderScan.closed e
private def nd (A : Layout) : T W := nF (HistoryNodePorts.node A.nodePorts)
private def ker (A : Layout) : T W := read (nd A) 5
private def inc (A : Layout) : T W := a (read (ker A) 4) (l (6*A.party.motif))
private def rowId (A : Layout) : T W :=
  .binary .div (minus (read (inc A) 1) (read (ker A).load 1)) (l A.histogramStride)
private def shapeRow (A : Layout) : T W :=
  a (times (read (inc A) 2) (l A.party.parties)) (l A.party.party)
private def grid (A : Layout) : T W := a (l A.party.kinds) (times (l 7) (shapeRow A))
private def page (A : Layout) : T W :=
  a (l A.catalogue) (times (l (HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap)) (shapeRow A))

private def live (A : Layout) (x : T W) : T W :=
  let mask : T W := .binary .mod (.binary .div (read (inc A) 5) (l (2^A.party.party))) (l 2)
  .select .lt (l A.party.motif) (read (ker A) 3) (.select .eq mask (l 1) x (l 0)) (l 0)

private def localCode (A : Layout) (sup : Bool) (j : ℕ) : T W :=
  read (page A) (if sup then HistoryPortCatalogue.supplyBase A.demandCap+j
    else HistoryPortCatalogue.demandBase+2*j)

private def demandTile (A : Layout) (j : ℕ) : T W :=
  read (page A) (HistoryPortCatalogue.demandBase+2*j+1)

private def enabledPort (A : Layout) (sup : Bool) (j : ℕ) (x : T W) : T W :=
  live A (.select .lt (l j) (read (page A) sup.toNat) x (l 0))

def logicalWidth (A : Layout) (sup : Bool) (j : ℕ) : T W :=
  let code := localCode A sup j
  let raw := match A.mode with
    | .shrink _ => (a (read (ker A).load (if sup then 3 else 8))
        (a (times (l (if sup then 8 else 2)) (rowId A)) code)).load
    | .refresh m h pad => (HeaderScan.closed (Diagonal.RefreshParty.width m h pad sup)).instantiate
        ![(ker A).load,read (ker A) 1,inc A,l A.party.party,code,l 0,l 0]
  enabledPort A sup j raw

def slot (A : Layout) (supply : Bool) (j : ℕ) := if supply then A.demandCap+j else j
def srcBase (A : Layout) (supply : Bool) (j : ℕ) := A.temp+(1+slot A supply j)*A.party.V
def gathers (A : Layout) := A.temp+1+2*(A.demandCap+A.supplyCap)
def supplyRows (A : Layout) := gathers A+2
def demandRows (A : Layout) := supplyRows A+2*A.supplyCap

private def oldBits (A : Layout) : T W :=
  (a (l A.nodePorts.starts) (nF (HistoryNodePorts.childCount A.nodePorts))).load

private def privateBank (A : Layout) (bank : ℕ) : T W :=
  let q := ⟨A.party.motif+2,A.party.party+2,2,bank⟩
  let s := HistoryScratch.sector A.party.motifs A.party.parties q
  a (l A.party.arena) (times (a (times (nF (HistoryNodePorts.id A.nodePorts)) (l A.party.V)) (l s)) (l A.party.V))

/-- Each active edge gets one disjoint V-word scratch aperture. Only its
actual logical width is touched. The short [base,length] and
[base,length,base-tile-width] port metadata is emitted at bounded degree. -/
def fields (A : Layout) : List (T W) :=
  let side (sup : Bool) (j : ℕ) := [l (srcBase A sup j),logicalWidth A sup j]
  let supply (j : ℕ) := [l (srcBase A true j),
    minus (logicalWidth A true j) (times (live A (read (inc A) 3)) (live A (read (grid A) 2)))]
  let demand (j : ℕ) := [l (srcBase A false j),logicalWidth A false j,enabledPort A false j (demandTile A j)]
  [l (A.temp+1)] ++ (List.range A.demandCap).flatMap (side false) ++
    (List.range A.supplyCap).flatMap (side true) ++ [privateBank A 2,live A (read (privateBank A 1) 1)] ++
    (List.range A.supplyCap).flatMap supply ++ (List.range A.demandCap).flatMap demand

/-- The thirteen actual operands of the per-port geometry ROM. -/
def sourceOperands (A : Layout) (sup : Bool) (j : ℕ) : Fin 13 → T W :=
  ![ker A,read (ker A) 1,inc A,l A.party.party,localCode A sup j,
    minus (.result 0) (l (srcBase A sup j)),nF (HistoryNodePorts.childList A.nodePorts),
    l A.nodePorts.nodes,l A.nodePorts.starts,nF (HistoryNodePorts.halves A.nodePorts),oldBits A,
    a (oldBits A) (nF (HistoryNodePorts.fresh A.nodePorts)),l A.privateStarts]

def geometryTerm (W : ℕ) (A : Layout) (sup : Bool) : Term W 1 13 :=
  match A.mode with
    | .shrink S => HistoryGeometryPointer.shrink W S sup
    | .refresh m h pad => HistoryGeometryPointer.refresh W m h pad sup

def sourceTerm (W : ℕ) (A : Layout) (sup : Bool) (j : ℕ) : T W :=
  let f := HistoryCommandParameter.replace (fun _ => (.literal 0 : Term W 0 0)) (geometryTerm W A sup)
  f.instantiate (sourceOperands A sup j)

def gatherOperands (A : Layout) : Fin 10 → T W :=
  ![minus (.result 0) (privateBank A 2),read (inc A) 3,read (grid A) 2,read (grid A) 0,
    read (grid A) 3,read (grid A) 4,read (page A) 2,l (supplyRows A),l (demandRows A),
    a (page A) (l (HistoryPortCatalogue.headerBase A.demandCap A.supplyCap))]

def gatherTerm (W : ℕ) (A : Layout) : T W :=
  (HeaderScan.closed HistoryPartyGather.formula).instantiate (gatherOperands A)


def headerTerm (W : ℕ) (A : Layout) : T W :=
  choice (minus (.result 0) (l A.temp)) 0 (fields A)

private theorem literal_binds (v : ℕ) : (l (W:=W) v).binds = 1 := rfl

private theorem select_binds (cmp : Comparison) (x y yes no : T W) :
    (Term.select cmp x y yes no).binds = x.binds + y.binds + yes.binds + no.binds + 1 := by
  simp [Term.select, Term.binds, Nat.add_assoc]

private theorem binary_binds (op : BinaryOp) (x y : T W) :
    (Term.binary op x y).binds = x.binds + y.binds + 1 := by
  simp [Term.binary, Term.binds, Nat.add_assoc]

private theorem load_binds (x : T W) : x.load.binds = x.binds + 1 := by
  simp [Term.load, Term.binds]

private def nodeCost := (HistoryNodePorts.node ⟨0,0,0,0⟩).work
private def idCost := (HistoryNodePorts.id ⟨0,0,0,0⟩).work

private theorem node_work_fixed (A : HistoryNodePorts.Layout) :
    (HistoryNodePorts.node A).work = nodeCost := rfl

private theorem id_work_fixed (A : HistoryNodePorts.Layout) :
    (HistoryNodePorts.id A).work = idCost := rfl

local macro "size_operands" : tactic => `(tactic|
  simp (config := {failIfUnchanged := false}) only [enabledPort, live, minus, privateBank,
    demandTile, localCode, rowId, grid, page, shapeRow, inc, ker, nd, read, a, times, nF,
    select_binds, binary_binds, load_binds, literal_binds, HeaderScan.binds_closed,
    Term.binds_instantiate, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, node_work_fixed, id_work_fixed])

private theorem choice_size {U : ℕ} (x : T W) (y : T U) (i j : ℕ)
    (xs : List (T W)) (ys : List (T U)) (h : x.binds=y.binds)
    (sizes : xs.map Term.binds=ys.map Term.binds) : (choice x i xs).binds=(choice y j ys).binds := by
  induction xs generalizing i j ys with
  | nil => cases ys with
    | nil => rfl
    | cons b ys => simp at sizes
  | cons a xs ih =>
    cases ys with
    | nil => simp at sizes
    | cons b ys =>
      simp only [List.map_cons, List.cons.injEq] at sizes
      simp only [choice, select_binds, literal_binds, h, sizes.1, ih (i+1) (j+1) ys sizes.2]

set_option maxHeartbeats 1000000 in
private theorem logical_work {U : ℕ} (A B : Layout) (mode : A.mode=B.mode) (q : Bool) (j : ℕ) :
    (logicalWidth (W:=W) A q j).binds=(logicalWidth (W:=U) B q j).binds := by
  cases ha : A.mode with
  | shrink S =>
    have hb := mode.symm.trans ha
    simp only [logicalWidth, ha, hb]
    size_operands
  | refresh m h pad =>
    have hb := mode.symm.trans ha
    simp only [logicalWidth, ha, hb]
    size_operands

set_option maxHeartbeats 1000000 in
theorem header_work {U : ℕ} (A B : Layout) (mode : A.mode=B.mode) (d : A.demandCap=B.demandCap)
    (s : A.supplyCap=B.supplyCap) : (headerTerm W A).binds=(headerTerm U B).binds := by
  have index : (minus (W:=W) (.result 0) (l A.temp)).binds =
      (minus (W:=U) (.result 0) (l B.temp)).binds := by
    simp only [minus, select_binds, binary_binds, literal_binds, Term.binds]
  have same : (fields (W:=W) A).map Term.binds = (fields (W:=U) B).map Term.binds := by
    simp only [fields, List.map_append, List.map_flatMap, List.map_cons,
      List.map_nil, d, s]
    size_operands
    all_goals simp only [logical_work (W:=W) (U:=U) A B mode]
  exact choice_size (W:=W) (U:=U) (minus (.result 0) (l A.temp)) (minus (.result 0) (l B.temp))
    0 0 (fields A) (fields B) index same

def sourceCost : Geometry→Bool→ℕ
  | .shrink S,q => (HistoryGeometryPointer.shrink 1 S q).binds+1000000
  | .refresh m h pad,q => (HistoryGeometryPointer.refresh 1 m h pad q).binds+1000000

private theorem sum_vector_cons {n : ℕ} (x : T W) (xs : Fin n → T W) :
    (∑ i, (Matrix.vecCons x xs i).binds) = x.binds + ∑ i, (xs i).binds := by
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]

set_option maxHeartbeats 1000000 in
private theorem source_operands_bound (W : ℕ) (A : Layout) (sup : Bool) (j : ℕ) :
    (∑ i, (sourceOperands (W:=W) A sup j i).binds) ≤ 1000000 := by
  simp only [sourceOperands, sum_vector_cons, Fin.sum_univ_zero, oldBits]
  size_operands
  have node : nodeCost = 13 := rfl
  have childList : (HistoryNodePorts.childList A.nodePorts).work = 16 := rfl
  have childCount : (HistoryNodePorts.childCount A.nodePorts).work = 16 := rfl
  have halves : (HistoryNodePorts.halves A.nodePorts).work = 16 := rfl
  have fresh : (HistoryNodePorts.fresh A.nodePorts).work = 149 := rfl
  have result : (Term.result 0 : T W).binds = 0 := rfl
  simp only [node, childList, childCount, halves, fresh, result]
  decide

private theorem source_instance_bound (g : Term W 1 13) (args : Fin 13 → T W) (price : ℕ)
    (tariff : g.binds + 1000000 = price) (inputs : (∑ i, (args i).binds) ≤ 1000000) :
    ((HistoryCommandParameter.replace (fun _ => (.literal 0 : Term W 0 0)) g).instantiate args).binds
      ≤ price := by
  have sub := HistoryCommandParameter.binds_replace (fun _ => (.literal 0 : Term W 0 0))
    g 1 le_rfl (fun _ => le_rfl)
  rw [Term.binds_instantiate]
  exact (Nat.add_le_add (sub.trans_eq (Nat.mul_one g.binds)) inputs).trans_eq tariff

section
attribute [local irreducible] HistoryGeometryPointer.shrink HistoryGeometryPointer.refresh
  Term.instantiate HistoryCommandParameter.replace

private theorem source_geometry_cost (W : ℕ) (A : Layout) (sup : Bool) :
    (geometryTerm W A sup).binds + 1000000 = sourceCost A.mode sup := by
  cases A with
  | mk party ports mode stride temp demand supply digit cat starts =>
    cases mode with
    | shrink S =>
      exact congrArg (fun n : ℕ => n + 1000000) (HistoryGeometryPointer.shrink_size W 1 S sup)
    | refresh m h pad =>
      exact congrArg (fun n : ℕ => n + 1000000)
        (HistoryGeometryPointer.refresh_size W 1 m h pad sup)

theorem source_bound (W : ℕ) (A : Layout) (sup : Bool) (j : ℕ) :
    (sourceTerm W A sup j).binds≤ sourceCost A.mode sup :=
  source_instance_bound (geometryTerm W A sup) (sourceOperands A sup j) (sourceCost A.mode sup)
    (source_geometry_cost W A sup) (source_operands_bound W A sup j)
end

set_option maxHeartbeats 1000000 in
theorem gather_work (W U : ℕ) (A B : Layout) : (gatherTerm W A).binds=(gatherTerm U B).binds := by
  have words : Finset.univ.sum (fun i => ((gatherOperands (W:=W) A) i).binds) =
      Finset.univ.sum (fun i => ((gatherOperands (W:=U) B) i).binds) := by
    simp only [gatherOperands, sum_vector_cons, Fin.sum_univ_zero]
    size_operands
    simp only [Term.binds]
  simpa only [gatherTerm, Term.binds_instantiate, HeaderScan.binds_closed] using
    congrArg (fun n : ℕ => HistoryPartyGather.formula.work + n) words

/-- The only expanded per-bit arrays are at the presently selected party.
After the gather completes, its pin map lives in its own per-node bank,
and the ephemeral V-word port apertures can be reused by another party. -/
def procedure (W : ℕ) (A : Layout) : Procedure W :=
  let table := fields (W:=W) A
  let init := PhysicalInputPhases.writing (headerTerm W A) Fin.elim0 A.temp table.length
  let scan (sup : Bool) («prefix» : Procedure W) (j : ℕ) :=
    let off := 2*slot A sup j
    «prefix».seq (HeaderScan.procedure (A.temp : Word W) off (off+1) (sourceTerm W A sup j))
  let d := (List.range A.demandCap).foldl (scan false) init
  let s := (List.range A.supplyCap).foldl (scan true) d
  let off := 2*(A.demandCap+A.supplyCap)
  s.seq (HeaderScan.procedure (A.temp : Word W) off (off+1) (gatherTerm W A))

/-- Numerical register values obtained from the current node, the selected
incident and the catalogue. All address arithmetic here uses machine words. -/
structure Selected (w : ℕ) where
  kernel : Word w
  incident : Word w
  kindPage : Word w
  portPage : Word w
  childIDs : Word w
  newHalves : Word w
  oldBits : Word w
  newBits : Word w
  privatePage : ℕ → Word w

def wordAt (mem : Memory W) (x : Word W) (j : ℕ) : Word W := mem (x+(j:Word W)).val

def cutWord (a b : Word W) : Word W := if a<b then 0 else a-b

def selected (A : Layout) (mem : Memory W) : Selected W :=
  let value (f : Formula 1) := f.value (fun _=>0) mem (fun _=>0)
  let node := value (HistoryNodePorts.node A.nodePorts)
  let kernel := wordAt mem node 5
  let incident := wordAt mem kernel 4+(6*A.party.motif : ℕ)
  let row := wordAt mem incident 2*(A.party.parties:Word W)+(A.party.party:Word W)
  let old := mem ((A.nodePorts.starts:Word W)+value (HistoryNodePorts.childCount A.nodePorts)).val
  let bank (j : ℕ) :=
    let q := ⟨A.party.motif+2,A.party.party+2,2,j⟩
    let i := HistoryScratch.sector A.party.motifs A.party.parties q
    (A.party.arena:Word W)+(value (HistoryNodePorts.id A.nodePorts)*(A.party.V:Word W)+(i:Word W))*(A.party.V:Word W)
  ⟨kernel,incident,(A.party.kinds:Word W)+7*row,(A.catalogue:Word W)+
    (HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap:Word W)*row,
    value (HistoryNodePorts.childList A.nodePorts),value (HistoryNodePorts.halves A.nodePorts),
    old,value (HistoryNodePorts.fresh A.nodePorts),bank⟩

def portCode (A : Layout) (mem : Memory W) (supply : Bool) (j : ℕ) :=
  wordAt mem (selected A mem).portPage (if supply then HistoryPortCatalogue.supplyBase A.demandCap+j
    else HistoryPortCatalogue.demandBase+2*j)

def sourceRegisters (A : Layout) (mem : Memory W) (supply : Bool) (j : ℕ) (bit : Word W) : Fin 13→Word W :=
  let R := selected A mem
  ![R.kernel,wordAt mem R.kernel 1,R.incident,(A.party.party:Word W),portCode A mem supply j,
    bit,R.childIDs,(A.nodePorts.nodes:Word W),(A.nodePorts.starts:Word W),R.newHalves,R.oldBits,
    R.oldBits+R.newBits,(A.privateStarts:Word W)]

private def independentOfRegisters {n : ℕ} : Formula n → Bool
  | .reg _ => false
  | .lit _ | .param _ => true
  | .load x => independentOfRegisters x
  | .cut x y | .op _ x y => independentOfRegisters x && independentOfRegisters y
  | .select _ x y yes no =>
    independentOfRegisters x && independentOfRegisters y &&
      independentOfRegisters yes && independentOfRegisters no

private theorem value_without_registers {n : ℕ} (f : Formula n)
    (data : Param → Word W) (mem : Memory W) (xs ys : Fin n → Word W)
    (independent : independentOfRegisters f = true) :
    f.value data mem xs = f.value data mem ys := by
  induction f <;> simp_all [independentOfRegisters, Formula.value, Bool.and_eq_true]

private theorem map_register_cons {α β : Type} {n : ℕ} (f : α → β) (x : α) (xs : Fin n → α) :
    f ∘ Matrix.vecCons x xs = Matrix.vecCons (f x) (f ∘ xs) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem map_register_empty {α β : Type} (f : α → β) :
    f ∘ (Matrix.vecEmpty : Fin 0 → α) = Matrix.vecEmpty :=
  funext (fun i => Fin.elim0 i)

private theorem operands_source (A : Layout) (mem : Memory W) (supply : Bool) (j : ℕ) (ptr : Word W) :
    (fun i => (sourceOperands A supply j i).eval Fin.elim0 mem (fun _=>ptr))=
      sourceRegisters A mem supply j (cutWord ptr (srcBase A supply j:Word W)) := by
  have fixed (f : Formula 1) (h : independentOfRegisters f = true) :
      (nF f).eval Fin.elim0 mem (fun _ => ptr) = f.value (fun _ => 0) mem (fun _ => 0) :=
    (HeaderScan.eval_closed f _ _ _).trans (value_without_registers f _ _ _ _ h)
  have node := fixed (HistoryNodePorts.node A.nodePorts) rfl
  have count := fixed (HistoryNodePorts.childCount A.nodePorts) rfl
  have children := fixed (HistoryNodePorts.childList A.nodePorts) rfl
  have halves := fixed (HistoryNodePorts.halves A.nodePorts) rfl
  have fresh := fixed (HistoryNodePorts.fresh A.nodePorts) rfl
  have cursor : (Term.result 0 : T W).eval Fin.elim0 mem (fun _ => ptr) = ptr := rfl
  change (fun t : T W => t.eval Fin.elim0 mem (fun _ => ptr)) ∘ sourceOperands A supply j = _
  simp only [sourceOperands, map_register_cons, map_register_empty, sourceRegisters, portCode,
    selected, wordAt, cutWord, localCode, oldBits, nd, ker, inc, shapeRow, page, read, a, times,
    minus, l, Term.eval_binary, Term.eval_load, Term.eval_literal, Term.eval_select, cursor,
    node, count, children, halves, fresh, Comparison.test, BinaryOp.eval, decide_eq_true_eq, Nat.cast_zero]

private theorem difference (ptr base : Word W) (start x : ℕ) (first : base.val=start)
    (atPtr : ptr.val=start+x) : cutWord ptr base=(x:Word W) := by
  have le : base≤ptr := by change base.val≤ptr.val;omega
  apply Fin.ext
  rw [cutWord,ite_eq_right (not_lt_of_ge le),Fin.sub_val_of_le le,Fin.val_cast_of_lt (by have := ptr.isLt;omega)]
  omega

/-- Executing the actual per-port source scanner invokes the geometry ROM with
its thirteen live inputs and the exact in-port bit offset. -/
theorem sourceTerm_value (A : Layout) (mem : Memory W) (sup : Bool) (j x : ℕ)
    (ptr : Word W) (atPtr : ptr.val=srcBase A sup j+x) :
    (sourceTerm W A sup j).eval Fin.elim0 mem (fun _=>ptr)=
      (geometryTerm W A sup).eval (fun _=>0) mem (sourceRegisters A mem sup j (x:Word W)) := by
  have h : srcBase A sup j<2^W := by have := ptr.isLt;omega
  rw [sourceTerm,Term.eval_instantiate,HistoryCommandParameter.eval_replace,operands_source,
    difference ptr (srcBase A sup j:Word W) (srcBase A sup j) x (Fin.val_cast_of_lt h) atPtr]
  rfl

/-- The actual bounded header row emitter, in public byte order. -/
def numericHeaderWords (A : Layout) (width : Bool→ℕ→Word W) (payload tile : ℕ→Word W)
    (mapBase mapCount : Word W) : List (Word W) :=
  let side (sup : Bool) (j : ℕ) := [(srcBase A sup j:Word W),width sup j]
  let output (j : ℕ) := [(srcBase A true j:Word W),payload j]
  let input (j : ℕ) := [(srcBase A false j:Word W),width false j,tile j]
  [((A.temp+1:ℕ):Word W)] ++ (List.range A.demandCap).flatMap (side false) ++
    (List.range A.supplyCap).flatMap (side true) ++ [mapBase,mapCount] ++
    (List.range A.supplyCap).flatMap output ++ (List.range A.demandCap).flatMap input


/-- The party flag combines the selected row count with its real party-mask bit. -/
def partyActive (A : Layout) (m : Memory W) : Prop :=
  let r := selected A m
  (A.party.motif:Word W)<wordAt m r.kernel 3 ∧
    BinaryOp.eval .mod (BinaryOp.eval .div (wordAt m r.incident 5) ((2^A.party.party:ℕ):Word W)) 2=1

def portActive (A : Layout) (m : Memory W) (sup : Bool) (j : ℕ) : Prop :=
  partyActive A m ∧ (j:Word W)<wordAt m (selected A m).portPage sup.toNat

def physicalWidth (A : Layout) (m : Memory W) (sup : Bool) (j : ℕ) : Word W :=
  let r := selected A m
  let stage := m r.kernel.val
  let code := portCode A m sup j
  let row := BinaryOp.eval .div (cutWord (wordAt m r.incident 1) (wordAt m stage 1)) (A.histogramStride:Word W)
  if portActive A m sup j then
    match A.mode with
    | .shrink _ => m (wordAt m stage (if sup then 3 else 8)+((if sup then 8 else 2 : Word W)*row+code)).val
    | .refresh n d pad => (Diagonal.RefreshParty.width n d pad sup).value (fun _=>0) m
        ![stage,wordAt m r.kernel 1,r.incident,(A.party.party:Word W),code,0,0]
  else 0

def payloadWidth (A : Layout) (m : Memory W) (j : ℕ) : Word W :=
  let r := selected A m
  let copies := if partyActive A m then wordAt m r.incident 3 else 0
  let code := if partyActive A m then wordAt m r.kindPage 2 else 0
  cutWord (physicalWidth A m true j) (copies*code)

def tileWidth (A : Layout) (m : Memory W) (j : ℕ) : Word W :=
  if portActive A m false j then wordAt m (selected A m).portPage (HistoryPortCatalogue.demandBase+2*j+1) else 0

def partyMapCount (A : Layout) (m : Memory W) : Word W :=
  if partyActive A m then wordAt m ((selected A m).privatePage 1) 1 else 0

def headerWords (A : Layout) (m : Memory W) : List (Word W) :=
  numericHeaderWords A (physicalWidth A m) (payloadWidth A m) (tileWidth A m)
    ((selected A m).privatePage 2) (partyMapCount A m)

private theorem read_eval (m : Memory W) (p : Word W) (x : T W) (j : ℕ) :
    (read x j).eval Fin.elim0 m (fun _=>p)=wordAt m (x.eval Fin.elim0 m (fun _=>p)) j := by
  simp only [read,a,l,Term.eval_load,Term.eval_binary,Term.eval_literal,BinaryOp.eval,wordAt]

private theorem k_eval (A : Layout) (m : Memory W) (p : Word W) :
    (ker A).eval Fin.elim0 m (fun _=>p)=(selected A m).kernel := by
  have fixed := value_without_registers (HistoryNodePorts.node A.nodePorts)
    (fun _=>0) m (fun _=>p) (fun _=>0) rfl
  simpa only [ker,read_eval,nd,nF,HeaderScan.eval_closed,selected] using
    congrArg (fun v => wordAt m v 5) fixed

private theorem i_eval (A : Layout) (m : Memory W) (p : Word W) :
    (inc A).eval Fin.elim0 m (fun _=>p)=(selected A m).incident := by
  simp only [inc,a,Term.eval_binary,read_eval,k_eval,l,Term.eval_literal,BinaryOp.eval]; rfl

private theorem grid_eval (A : Layout) (m : Memory W) (p : Word W) :
    (grid A).eval Fin.elim0 m (fun _=>p)=(selected A m).kindPage := by
  simp only [grid,shapeRow,a,times,l,Term.eval_binary,Term.eval_literal,read_eval,i_eval,BinaryOp.eval]; rfl

private theorem page_eval (A : Layout) (m : Memory W) (p : Word W) :
    (page A).eval Fin.elim0 m (fun _=>p)=(selected A m).portPage := by
  simp only [page,shapeRow,a,times,l,Term.eval_binary,Term.eval_literal,read_eval,i_eval,BinaryOp.eval]; rfl

private theorem code_eval (A : Layout) (m : Memory W) (p : Word W) (sup : Bool) (j : ℕ) :
    (localCode A sup j).eval Fin.elim0 m (fun _=>p)=portCode A m sup j := by
  rw [localCode,read_eval,page_eval,portCode]

private theorem bank_eval (A : Layout) (m : Memory W) (p : Word W) (j : ℕ) :
    (privateBank A j).eval Fin.elim0 m (fun _=>p)=(selected A m).privatePage j := by
  have fixed := value_without_registers (HistoryNodePorts.id A.nodePorts) (fun _=>0) m (fun _=>p) (fun _=>0) rfl
  simp only [privateBank,a,times,l,nF,Term.eval_binary,Term.eval_literal,HeaderScan.eval_closed,BinaryOp.eval,fixed]; rfl

private theorem minus_eval (x y : T W) (m : Memory W) (p : Word W) :
    (minus x y).eval Fin.elim0 m (fun _=>p)=cutWord (x.eval Fin.elim0 m (fun _=>p)) (y.eval Fin.elim0 m (fun _=>p)) := by
  simp only [minus,cutWord,l,Term.eval_select,Term.eval_binary,Term.eval_literal,Comparison.test,BinaryOp.eval,decide_eq_true_eq,Nat.cast_zero]

private theorem live_eval (A : Layout) (m : Memory W) (x : T W) (p : Word W) :
    (live A x).eval Fin.elim0 m (fun _=>p)=if partyActive A m then x.eval Fin.elim0 m (fun _=>p) else 0 := by
  simp only [live,read_eval,k_eval,i_eval,l,partyActive,Term.eval_binary,Term.eval_literal,
    Term.eval_select,Comparison.test,decide_eq_true_eq,beq_iff_eq,Nat.cast_zero,Nat.cast_one]
  by_cases h : (A.party.motif:Word W)<wordAt m (selected A m).kernel 3 <;> simp [h]

private theorem enabled_eval (A : Layout) (m : Memory W) (sup : Bool) (j : ℕ) (x : T W) (p : Word W) :
    (enabledPort A sup j x).eval Fin.elim0 m (fun _=>p)=
      if portActive A m sup j then x.eval Fin.elim0 m (fun _=>p) else 0 := by
  simp only [enabledPort,live_eval,read_eval,page_eval,l,Term.eval_literal,
    Term.eval_select,Comparison.test,decide_eq_true_eq,portActive,Nat.cast_zero]
  by_cases y : partyActive A m <;> simp [y]

private theorem width_eval (A : Layout) (m : Memory W) (sup : Bool) (j : ℕ) (p : Word W) :
    (logicalWidth A sup j).eval Fin.elim0 m (fun _=>p)=physicalWidth A m sup j := by
  rw [logicalWidth,enabled_eval,physicalWidth]
  by_cases active : portActive A m sup j
  · simp only [ite_eq_left active]
    cases ha : A.mode with
    | shrink S =>
      simp only [a,times,rowId,Term.eval_binary,Term.eval_load,read_eval,i_eval,k_eval,
        minus_eval,l,Term.eval_literal,code_eval,BinaryOp.eval]
      cases sup <;> rfl
    | refresh n d pad =>
      rw [Term.eval_instantiate,HeaderScan.eval_closed]
      apply congrArg ((Diagonal.RefreshParty.width n d pad sup).value (fun _=>0) m)
      change (fun t : T W => t.eval Fin.elim0 m (fun _=>p)) ∘ _ = _
      simp only [map_register_cons,map_register_empty,read_eval,k_eval,i_eval,code_eval,
        Term.eval_load,l,Term.eval_literal,Nat.cast_zero]
  · simp only [ite_eq_right active]

/-- Evaluating every real header expression recovers the fixed ordering of the
old/new aperture records, the private-party map, and the two port directories. -/
theorem fields_value (A : Layout) (m : Memory W) (p : Word W) :
    (fields (W:=W) A).map (fun t=>t.eval Fin.elim0 m (fun _=>p))=headerWords A m := by
  unfold fields headerWords numericHeaderWords
  simp only [List.map_append,List.map_flatMap,List.map_cons,List.map_nil,width_eval,enabled_eval,live_eval,minus_eval,demandTile,times,Term.eval_binary,BinaryOp.eval,
    read_eval,i_eval,page_eval,grid_eval,bank_eval,l,Term.eval_literal,payloadWidth,tileWidth,partyMapCount]

private theorem choice_at (m : Memory W) (p : Word W) (t : T W) (start idx : ℕ) (xs : List (T W))
    (pos : idx<xs.length) (room : start+idx<2^W)
    (key : t.eval Fin.elim0 m (fun _=>p)=((start+idx:ℕ):Word W)) :
    (choice t start xs).eval Fin.elim0 m (fun _=>p)=(xs[idx]).eval Fin.elim0 m (fun _=>p) := by
  induction xs generalizing start idx with
  | nil => simp at pos
  | cons a xs ih =>
    rw [choice,Term.eval_select,l,Term.eval_literal,key]
    cases idx with
    | zero => simp [Comparison.test]
    | succ idx =>
      have loc : start<2^W := by omega
      have ne : ((start+(idx+1):ℕ):Word W)≠(start:Word W) := by
        intro eq
        have diff := congrArg Fin.val eq
        rw [Fin.val_cast_of_lt room,Fin.val_cast_of_lt loc] at diff
        omega
      simp only [Comparison.test,beq_iff_eq,ite_eq_right ne,List.getElem_cons_succ]
      exact ih (start+1) idx (by simpa using pos) (by omega) (by convert key using 2; omega)

private theorem equalEntry {α : Type} {xs ys : List α} (h : xs=ys) (i : ℕ)
    (hx : i<xs.length) (hy : i<ys.length) : xs[i]=ys[i] := by
  cases h
  rfl

/-- Each address of the initially emitted header is its actual numeric row. -/
theorem headerTerm_at (A : Layout) (m : Memory W) (p : Word W) (idx : ℕ)
    (atPtr : p.val=A.temp+idx) (len : idx<(headerWords A m).length) :
    (headerTerm W A).eval Fin.elim0 m (fun _=>p)=(headerWords A m)[idx] := by
  have fmt := fields_value A m p
  have pos : idx<(fields (W:=W) A).length := by simpa [←fmt] using len
  have room : A.temp<2^W := by have := p.isLt;omega
  rw [headerTerm,choice_at m p _ 0 idx _ pos (by have := p.isLt;omega)]
  · have mapped := equalEntry fmt idx (by simpa only [List.length_map] using pos) len
    simpa only [List.getElem_map] using mapped
  · simpa only [minus,l,Term.eval_select,Term.eval_binary,Term.eval_literal,Term.eval,
      Comparison.test,BinaryOp.eval,cutWord,decide_eq_true_eq,Nat.zero_add,Nat.cast_zero] using
      difference p (A.temp:Word W) A.temp idx (Fin.val_cast_of_lt room) atPtr

/-- The gather's non-register inputs are precisely the two metadata banks and
selected immutable demand-digit page. -/
def gatherLayout (A : Layout) (mem : Memory W) : HistoryPartyGather.Layout :=
  let r := selected A mem
  ⟨(wordAt mem r.incident 3).val,(wordAt mem r.kindPage 2).val,(wordAt mem r.kindPage 0).val,
    (wordAt mem r.kindPage 3).val,(wordAt mem r.kindPage 4).val,(wordAt mem r.portPage 2).val,
    supplyRows A,demandRows A,(r.portPage+(HistoryPortCatalogue.headerBase A.demandCap A.supplyCap:Word W)).val⟩

private theorem operands_gather (A : Layout) (mem : Memory W) (ptr : Word W) :
    (fun i => (gatherOperands A i).eval Fin.elim0 mem (fun _ => ptr))=
      fun i => ((gatherLayout A mem).args (cutWord ptr ((selected A mem).privatePage 2)).val i : Word W) := by
  have cursor : (Term.result 0 : T W).eval Fin.elim0 mem (fun _=>ptr) = ptr := rfl
  change (fun t : T W => t.eval Fin.elim0 mem (fun _=>ptr)) ∘ gatherOperands A =
    (fun z : ℕ => (z:Word W)) ∘ (gatherLayout A mem).args (cutWord ptr ((selected A mem).privatePage 2)).val
  simp only [gatherOperands,gatherLayout,HistoryPartyGather.Layout.args,map_register_cons,map_register_empty,
    minus_eval,bank_eval,cursor,read_eval,i_eval,grid_eval,page_eval,a,l,Term.eval_binary,Term.eval_literal,
    BinaryOp.eval,Fin.cast_val_eq_self]

/-- Native evaluation of the final selected party gather, including its
physical output offset, uses the words actually present in the port arrays. -/
theorem gatherTerm_value (A : Layout) (mem : Memory W) (ptr : Word W) (x : ℕ)
    (atPtr : ptr.val=((selected A mem).privatePage 2).val+x)
    (fit : HistoryPartyGather.formula.Fits W (fun _=>0) (fun j=>(mem j).val) ((gatherLayout A mem).args x)) :
    (gatherTerm W A).eval Fin.elim0 mem (fun _=>ptr)=
      (HistoryPartyGather.gather (gatherLayout A mem) (fun j=>(mem j).val) x : Word W) := by
  have h : x<2^W := by have := ptr.isLt;omega
  rw [gatherTerm,Term.eval_instantiate,operands_gather,difference ptr _ _ x rfl atPtr,Fin.val_cast_of_lt h,HeaderScan.eval_closed]
  have eq := Formula.value_eq_natural HistoryPartyGather.formula (fun _=>0) (fun j=>(mem j).val) _ fit
  rw [HistoryPartyGather.natural] at eq
  simpa only [Nat.cast_zero,Fin.cast_val_eq_self] using eq

/-- The live mask follows the actual selected incidence bit even when the
header is read from a later chronological scan. -/
theorem partyActive_iff (A : Layout) (m : Memory W) (motif : A.party.motif<2^W)
    (mask : 2^A.party.party<2^W) (two : 2<2^W) :
    partyActive A m ↔ A.party.motif<(wordAt m (selected A m).kernel 3).val ∧
      (wordAt m (selected A m).incident 5).val.testBit A.party.party=true := by
  let v := wordAt m (selected A m).incident 5
  let k := A.party.party
  have q : v.val/2^k<2^W := (Nat.div_le_self ..).trans_lt v.isLt
  have r : v.val/2^k%2<2^W := (Nat.mod_lt _ (by decide : 0<2)).trans two
  have exactDiv : BinaryOp.eval .div v ((2^k:ℕ):Word W) = ((v.val/2^k:ℕ):Word W) := by
    simpa only [Fin.cast_val_eq_self] using WordQuotients.div_at v.val (2^k) v.isLt mask
  have exactMod : BinaryOp.eval .mod ((v.val/2^k:ℕ):Word W) 2 = ((v.val/2^k%2:ℕ):Word W) := by
    simpa only [Nat.cast_ofNat] using WordQuotients.mod_at (v.val/2^k) 2 q two
  change ((A.party.motif:Word W).val<_ ∧ BinaryOp.eval .mod (BinaryOp.eval .div v ((2^k:ℕ):Word W)) 2=1) ↔ _
  rw [Fin.val_cast_of_lt motif,exactDiv,exactMod,Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_true_eq]
  apply and_congr_right
  intro _
  constructor
  · intro he
    have u := congrArg Fin.val he
    simpa only [Fin.val_cast_of_lt r,Fin.val_one',Nat.mod_eq_of_lt (by omega : 1<2^W)] using u
  · intro he
    simpa only [Nat.cast_one] using congrArg (fun z : ℕ => (z:Word W)) he

theorem portActive_iff (A : Layout) (m : Memory W) (sup : Bool) (j : ℕ) (hj : j<2^W) :
    portActive A m sup j ↔ partyActive A m ∧ j<(wordAt m (selected A m).portPage sup.toNat).val := by
  change (_ ∧ (j:Word W).val<_) ↔ _
  rw [Fin.val_cast_of_lt hj]

/-- Address of an active AB/CD or supply width loaded while writing the bounded S17 header. -/
def issuedCell (J : Layout) {W : ℕ} (m : Memory W) (side : Bool) (i : ℕ) : ℕ :=
  let sel:=selected J m
  let stage:=m sel.kernel.val
  let row:=BinaryOp.eval .div (cutWord (wordAt m sel.incident 1) (wordAt m stage 1)) (J.histogramStride:Word W)
  (wordAt m stage (if side then 3 else 8)+((if side then 8 else 2:Word W)*row+portCode J m side i)).val

theorem shrink_address (A : Layout) (m : Memory W) (sup : Bool) (j row code hist tab : ℕ)
    (stride : 0<A.histogramStride)
    (strideFit : A.histogramStride<2^W)
    (histRow : (wordAt m (selected A m).incident 1).val=hist+row*A.histogramStride)
    (histBase : (wordAt m (m (selected A m).kernel.val) 1).val=hist)
    (port : portCode A m sup j=(code:Word W))
    (bank : wordAt m (m (selected A m).kernel.val) (if sup then 3 else 8)=(tab:Word W))
    (space : tab+((if sup then 8 else 2)*row+code)<2^W) :
    issuedCell A m sup j=(tab+((if sup then 8 else 2)*row+code)) := by
  have fit : row*A.histogramStride<2^W := by have := (wordAt m (selected A m).incident 1).isLt; omega
  have sub := difference _ _ _ _ histBase histRow
  have quotient := WordQuotients.div_at (row*A.histogramStride) A.histogramStride fit strideFit
  rw [Nat.mul_div_cancel _ stride] at quotient
  have strideWord : (if sup then (8:Word W) else 2)=((if sup then 8 else 2 : ℕ):Word W) := by
    cases sup <;> rfl
  simp only [issuedCell,sub,quotient,port,bank,strideWord]
  simpa only [Nat.cast_add,Nat.cast_mul] using (Fin.val_cast_of_lt space)

/-- The indexed width of a shrink port is the chosen row in the demand or
issued-width column. The row number comes from its actual histogram address. -/
theorem shrink_width (A : Layout) (m : Memory W) (S : Graph.Stage) (sup : Bool) (j row code hist tab : ℕ)
    (kind : A.mode=.shrink S) (enabled : portActive A m sup j) (stride : 0<A.histogramStride)
    (strideFit : A.histogramStride<2^W)
    (histRow : (wordAt m (selected A m).incident 1).val=hist+row*A.histogramStride)
    (histBase : (wordAt m (m (selected A m).kernel.val) 1).val=hist)
    (port : portCode A m sup j=(code:Word W))
    (bank : wordAt m (m (selected A m).kernel.val) (if sup then 3 else 8)=(tab:Word W))
    (space : tab+((if sup then 8 else 2)*row+code)<2^W) :
    physicalWidth A m sup j=m (tab+((if sup then 8 else 2)*row+code)) := by
  simp only [physicalWidth,ite_eq_left enabled,kind]
  exact congrArg m (shrink_address A m sup j row code hist tab stride strideFit histRow histBase port bank space)

def refreshWidthRegisters (A : Layout) (m : Memory W) (sup : Bool) (j : ℕ) : Fin 7→Word W :=
  let r := selected A m
  ![m r.kernel.val,wordAt m r.kernel 1,r.incident,(A.party.party:Word W),portCode A m sup j,0,0]

theorem refresh_width (A : Layout) (m : Memory W) (n d pad : ℕ) (sup : Bool) (j : ℕ)
    (mode : A.mode=.refresh n d pad) (enabled : portActive A m sup j) :
    physicalWidth A m sup j=(HeaderScan.closed (Diagonal.RefreshParty.width n d pad sup)).eval
      Fin.elim0 m (refreshWidthRegisters A m sup j) := by
  simp only [physicalWidth,ite_eq_left enabled,mode,HeaderScan.eval_closed,refreshWidthRegisters]

/-- Compacted payload widths exclude the appended selectors for exactly the
number of real copies in this motif. -/
theorem payloadWidth_eq (A : Layout) (m : Memory W) (j hist copies bits : ℕ)
    (active : partyActive A m) (copiesRead : wordAt m (selected A m).incident 3=(copies:Word W))
    (codeRead : wordAt m (selected A m).kindPage 2=(bits:Word W))
    (total : physicalWidth A m true j=((hist+copies*bits:ℕ):Word W))
    (fits : hist+copies*bits<2^W) : payloadWidth A m j=(hist:Word W) := by
  simp only [payloadWidth,ite_eq_left active,copiesRead,codeRead,total,←Nat.cast_mul]
  apply difference _ _ (copies*bits) hist
  · exact Fin.val_cast_of_lt (by omega)
  · rw [Fin.val_cast_of_lt fits,Nat.add_comm]

section Party
open Diagonal LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector Diagonal.MotifOuterTerms Diagonal.MotifBinaryPacking
open Diagonal.HistogramTileNetwork
variable {J E S H : Type*} [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] {k e n d r h p : ℕ}
  (D : PortGraph J E) (G : Supply J S) (j : J) (base w : E → ℕ)
  (B : Header (D.Port j) H (fun a => base a.1.1) k n)
  (portsAt : Fin e ≃ (ports G).Port j) (sw : H → S → ℕ) (z : Histogram H r)
  (old : (a : D.Port j) → Fin (w a.1.1) → BitSource h p)
  (fresh : (a : (ports G).Port j) → Fin (histWidth sw z a.1.1+r*k) → BitSource h p)

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
/-- Every output of the native gather is the actual source of its selected
party. The same pointer is used by `directParty` and `occupiedTree.localWire`. -/
theorem gatherTerm_party (A : Layout) (m : Memory W) (ptr : Word W)
    (x : Fin (r*(e*k)+(r*B.arity+e*(r*d))))
    (key : ptr.val=((selected A m).privatePage 2).val+x.val)
    (fit : HistoryPartyGather.formula.Fits W (fun _=>0) (fun j=>(m j).val) ((gatherLayout A m).args x.val))
    (image : HistoryPartyGather.Image (d:=d) D G j base w B portsAt sw z old fresh (gatherLayout A m)
      (fun j=>(m j).val)) :
    (gatherTerm W A).eval Fin.elim0 m (fun _=>ptr)=
      (BitLayout.sourceAddress (partyPointer D G j base w B portsAt sw z old fresh x):Word W) := by
  rw [gatherTerm_value A m ptr x.val key fit,HistoryPartyGather.gather_eq D G j base w B portsAt sw z old fresh image x]
end Party

section Source
open Diagonal Diagonal.CompressorPacking.Native HistoryGeometryPointer
variable {h p : ℕ} (A : Layout) (m : Memory W) (q : Bool) (j bit : ℕ) (ptr : Word W)
local notation "reg" => sourceRegisters A m q j (bit:Word W)

/-- The actual compact-kernel and incident pointer are supplied to the native
shrink field scanner before interpreting its old, new or absorbed edge. -/
theorem shrink_source (S : Graph.Stage) (mode : A.mode=.shrink S) (key : ptr.val=srcBase A q j+bit)
    (loc : Fin 4→ℕ) (s : BitSource h p)
    (origin : ∀ i : Fin 4,(HeaderScan.closed (ShrinkStage.BitOrigins.lookup S q (.reg 0) (.reg 2)
      (.reg 3) (.reg 4) (.reg 5) (.lit i.val) : Formula 13)).eval Fin.elim0 m reg=(loc i:Word W))
    (fits : ReadFits m reg loc) (read : HistoryScopeAddress.Read (layoutOf reg) (fun n=>(m n).val) loc s) :
    (sourceTerm W A q j).eval Fin.elim0 m (fun _=>ptr)=(BitLayout.sourceAddress s:Word W) := by
  rw [sourceTerm_value A m q j bit ptr key,geometryTerm,mode]
  exact read_shrink S q m reg loc s origin fits read

private theorem refresh_source (degree height pad : ℕ) (mode : A.mode=.refresh degree height pad)
    (key : ptr.val=srcBase A q j+bit) (loc : Fin 4→ℕ) (s : BitSource h p)
    (fields : ∀ i : Fin 4,(HeaderScan.closed (Diagonal.RefreshParty.lookup degree height pad q)).eval
      Fin.elim0 m (refreshRegs m reg i)=(loc i:Word W))
    (fits : ReadFits m reg loc) (read : HistoryScopeAddress.Read (layoutOf reg) (fun n=>(m n).val) loc s) :
    (sourceTerm W A q j).eval Fin.elim0 m (fun _=>ptr)=(BitLayout.sourceAddress s:Word W) := by
  rw [sourceTerm_value A m q j bit ptr key,geometryTerm,mode]
  exact read_refresh degree height pad q m reg loc s fields fits read
end Source

section Refresh
open Diagonal Computability.VPVNP.Compression Diagonal.CompressorPacking.Native Diagonal.RefreshParty
open Diagonal.RefreshDemandRows Diagonal.RefreshTies RAM.MotifRows HistoryGeometryPointer
variable {v a t h pad hidden pins : ℕ} {G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t)}
    {C : SlotImage.Columns} {split : ℕ} {w : SlotImage.RefreshInput v a t → ℕ}
    (A : Layout) (m : Memory W) (mode : A.mode=.refresh (mPort a) h pad)
    (j bit : ℕ) (ptr : Word W)

private theorem refreshSource_same {a b : Fin 7→Word W} (s : Source m a G C split w) (eq : b 0=a 0) :
    Source m b G C split w := by
  exact s.reopen (congrArg Fin.val eq) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

include mode in
theorem refresh_demand_width (enabled : portActive A m false j) (z : Block v t)
    (store : Source m (refreshWidthRegisters A m false j) G C split w) (block : (m (selected A m).incident.val).val=blockId z)
    (p s : Fin (mPort a)) (dir side : Bool) (party : (A.party.party:Word W).val=p.val)
    (code : (portCode A m false j).val=((if dir then 2 else 0)+(if side then 1 else 0))*mPort a+s.val)
    (banks : 3*mPort a<2^W) (lane : 2^t<2^W) :
    physicalWidth A m false j=(SlotImage.demandWidth w (addr (arrival G (tagOrdinal a).symm) z
      (denseEnds p (dir,side,s)).1.1):Word W) := by
  rw [refresh_width A m _ h pad false j mode enabled]
  exact demand_width_native store z block p s dir side party code banks lane

def denseLocation (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (w : SlotImage.RefreshInput v a t→ℕ) (h pad : ℕ) (z : Block v t) (p s : Fin (mPort a))
    (dir side : Bool) (bit : ℕ) (i : Fin 4) :=
  component (demandLocation (h:=h) (pad:=pad) (arrival G (tagOrdinal a).symm) (SlotImage.demandWidth w)
    z p (denseEnds p (dir,side,s)) bit) i.val

set_option maxHeartbeats 1200000 in
include mode in
/-- The refresh demand source uses the actual old graph table, dense party
number and the numerical four-field location at its selected bit. -/
theorem refresh_demand_source (z : Block v t) (p s : Fin (mPort a)) (dir side : Bool)
    (key : ptr.val=srcBase A false j+bit) (store : Source m (refreshWidthRegisters A m false j) G C split w)
    (block : (m (selected A m).incident.val).val=blockId z) (party : (A.party.party:Word W).val=p.val)
    (code : (portCode A m false j).val=((if dir then 2 else 0)+(if side then 1 else 0))*mPort a+s.val)
    (banks : 3*mPort a<2^W) (lane : 2^t<2^W) (space : 4≤2^W) (target : BitSource hidden pins)
    (fits : ReadFits m (sourceRegisters A m false j (bit:Word W)) (denseLocation G w h pad z p s dir side bit))
    (scope : HistoryScopeAddress.Read (layoutOf (sourceRegisters A m false j (bit:Word W))) (fun x => (m x).val)
      (denseLocation G w h pad z p s dir side bit) target) :
    (sourceTerm W A false j).eval Fin.elim0 m (fun _=>ptr)=(BitLayout.sourceAddress target:Word W) := by
  refine refresh_source A m false j bit ptr (mPort a) h pad mode key
    (denseLocation G w h pad z p s dir side bit) target ?_ fits scope
  intro i
  let r := refreshRegs m (sourceRegisters A m false j (bit:Word W)) i
  have old : Source m r G C split w := refreshSource_same m store rfl
  have bitFit : bit<2^W := by have := ptr.isLt;omega
  have bitAt : (r 5).val=bit := Fin.val_cast_of_lt bitFit
  have fieldAt : (r 6).val=i.val := Fin.val_cast_of_lt (i.isLt.trans_le space)
  have go := demand_native (h:=h) (pad:=pad) old z block p s dir side party code banks lane
  rw [bitAt,fieldAt] at go
  exact go

def sparseLocationWords (h pad : ℕ) (s : Fin h) (side : Bool) (bit width : ℕ) (i : Fin 4) :=
  component ⟨if bit<width then 2 else 0,0,1+(if side then 1+h+pad else 0)+s.val,bit⟩ i.val

variable (store : Source m (refreshWidthRegisters A m true j) G C split w) (siteCount : ℕ) (siteBound : (wordAt m (selected A m).kernel 1).val < siteCount)
    (s : Fin h) (side : Bool) (code : (portCode A m true j).val=(if side then h else 0)+s.val)
    (width : ℕ) (row : (m ((m ((m (selected A m).kernel.val).val+40)).val + (((wordAt m (selected A m).kernel 1).val * (2*(1+h+pad))+(1+(if side then 1+h+pad else 0)+s.val))*4+2))).val=width)
    (room : (m ((m (selected A m).kernel.val).val+40)).val + siteCount*(2*(1+h+pad))*4≤2^W) (degree : h<2^W)

include mode store siteCount siteBound s side code row room degree in
theorem refresh_supply_width (enabled : portActive A m true j) : physicalWidth A m true j=(width:Word W) := by
  apply (refresh_width A m (mPort a) h pad true j mode enabled).trans
  exact RefreshParty.supply_width_native (pad := pad) store siteCount siteBound s side code width
    (by
      change (m ((m ((m (selected A m).kernel.val).val + 40)).val +
        ((wordAt m (selected A m).kernel 1).val * (2 * (1 + h + pad)) +
          (1 + (if side then 1 + h + pad else 0) + s.val)) * 4 + 2)).val = width
      simpa only [Nat.add_assoc] using row) room degree

set_option maxHeartbeats 1200000 in
include mode store siteCount siteBound s side code row room degree in
/-- Each bit in the selected sparse half uses its real four-word retained
half row to decide whether this is the fresh pin or an empty location. -/
theorem refresh_supply_source (key : ptr.val=srcBase A true j+bit) (space : 4≤2^W) (target : BitSource hidden pins)
    (fits : ReadFits m (sourceRegisters A m true j (bit:Word W)) (sparseLocationWords h pad s side bit width))
    (scope : HistoryScopeAddress.Read (layoutOf (sourceRegisters A m true j (bit:Word W))) (fun x => (m x).val)
      (sparseLocationWords h pad s side bit width) target) :
    (sourceTerm W A true j).eval Fin.elim0 m (fun _=>ptr)=(BitLayout.sourceAddress target:Word W) := by
  refine refresh_source A m true j bit ptr (mPort a) h pad mode key
    (sparseLocationWords h pad s side bit width) target ?_ fits scope
  intro i
  let r := refreshRegs m (sourceRegisters A m true j (bit:Word W)) i
  have old : Source m r G C split w := refreshSource_same m store rfl
  have result := RefreshParty.supply_native (pad := pad) old siteCount siteBound s side code width
    (by
      change (m ((m ((m (selected A m).kernel.val).val + 40)).val +
        ((wordAt m (selected A m).kernel 1).val * (2 * (1 + h + pad)) +
          (1 + (if side then 1 + h + pad else 0) + s.val)) * 4 + 2)).val = width
      simpa only [Nat.add_assoc] using row) room degree
  have bitValue : (r 5).val = bit := by
    change (bit : Word W).val = bit
    exact Fin.val_cast_of_lt (by have := ptr.isLt; omega)
  have fieldValue : (r 6).val = i.val := by
    change (i.val : Word W).val = i.val
    exact Fin.val_cast_of_lt (i.isLt.trans_le space)
  rw [bitValue, fieldValue] at result
  exact result
end Refresh

section ShrinkDemand
open Diagonal Diagonal.CompressorPacking Diagonal.CompressorPacking.Native
open Computability.VPVNP.Compression ShrinkStage Diagonal.CompressorPacking.Native.Placement HistoryGeometryPointer
set_option quotPrecheck false
open private BitOrigins.requestWord from OAI.ThreeFlat.Diagonal.ShrinkDemandCD
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {N W c t l hidden pins : ℕ}
    {S₀ : Graph.Stage} {P : PackingData B H (BitWord t) (BitWord l) S₀.degree (c+1)}
    {E : Codec B W (c+1) t l} {b : B ≃ Fin N} {hc : 2≤c+1}
    {prior : Arc B H (BitWord t) (BitWord l) S₀.degree (c+1)→ℕ}
local notation "shrinkStage" => ChildRows.withFree S₀ c
local notation "code" => Demand.key P (baseNat b)
local notation "num" => motifNumbers P code hc
local notation "Q" => (3*(2^(c+1)*S₀.degree)/4)
variable (A : Layout) (mem : Memory W) (mode : A.mode=.shrink (ChildRows.withFree S₀ c)) (p : Pointers) (lay : Bool)
    (issued : P.Motif→Fin 8→ℕ) (m : P.Motif) (partyId : Fin 6) (j : ℕ) (port : demandGraph.Port partyId)
    (bit : Fin (demandWidth P prior (motifNumbers P (Demand.key P (baseNat b)) hc) m port.val.1))
    (ptr : Word W) (hQ : 0 < 3*(2^(c+1)*S₀.degree)/4)
local notation "regs" => sourceRegisters A mem false j (bit.val:Word W)
local notation "sourceLocation" => fun field : Fin 4 =>
  BitOrigins.requestWord (S₀ := S₀) (P := P) (prior := prior) (q := Q)
    code hQ num m port.val.2 port.val.1 bit (motifNumbers_bundle P code hc) lay
    (partySite P lay m partyId) (congrArg (partySite P lay m) port.property) field

set_option maxHeartbeats 800000 in
include mode hQ in
theorem shrink_demand_source (key : ptr.val=srcBase A false j+bit.val)
    (I : Resident.Input shrinkStage P b hc lay p (selected A mem).kernel prior issued mem)
    (number : ∀u,E.base u=((b u).val:Word W))
    (add : ∀u v,slotCode (w:=W) P (u+v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
    (sub : ∀u v,slotCode (w:=W) P (u-v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
    (graphRoom : p.oldGraph+6*(N*(shrinkStage).degree)≤2^W)
    (row : mem (selected A mem).incident.val=(code m.val:Word W))
    (size : (shrinkStage).degree<2^W ∧ 2^t<2^W ∧ 2^l<2^W) (cw : c+1<W) (fit : 4≤2^W)
    (partyVal : (A.party.party:Word W).val=partyId.val) (edgeVal : (portCode A mem false j).val=port.val.1.val)
    (widthFit : ∀ a,prior a<2^W) (totalFit : thickWidth P prior (P.bundle m)<2^W)
    (qFit : Q<2^W) (target : BitSource hidden pins) (rooms : ReadFits mem regs sourceLocation)
    (scope : HistoryScopeAddress.Read (layoutOf regs) (fun z=>(mem z).val) sourceLocation target) :
    (sourceTerm W A false j).eval Fin.elim0 mem (fun _=>ptr)=(BitLayout.sourceAddress target:Word W) := by
  apply shrink_source A mem false j bit.val ptr shrinkStage mode key sourceLocation target _ rooms scope
  intro k
  have reading := BitOrigins.selected_demand (S₀:=S₀) (P:=P) (b:=b) (E:=E) (prior:=prior) (hc:=hc) hQ p lay issued regs m partyId port bit k I number add sub
    graphRoom row size cw fit partyVal edgeVal rfl widthFit totalFit qFit
  simpa only [HeaderScan.eval_closed,Formula.eval_compile,Function.comp_def] using reading
end ShrinkDemand

/-- On a live party, writing the header must preserve the inputs of its later rows. -/
structure HeaderFootprint (A : Layout) (input : Memory W) (lo hi : ℕ) : Prop where
  stable : ∀{m},DescriptorScan.agreesOutside lo hi m input → headerWords A m=headerWords A input

/-- The chosen node and private arena sector use the current chronology cursor. -/
def nodeWord (A : Layout) (m : Memory W) : Word W :=
  (HistoryNodePorts.node A.nodePorts).value (fun _=>0) m (fun _=>0)

theorem id_stable (A : Layout) {m old : Memory W}
    (cursor : m ((A.nodePorts.cursor:Word W)).val=old ((A.nodePorts.cursor:Word W)).val) :
    (HistoryNodePorts.id A.nodePorts).value (fun _=>0) m (fun _=>0)=
      (HistoryNodePorts.id A.nodePorts).value (fun _=>0) old (fun _=>0) := by
  exact congrArg (fun x : Word W => if Comparison.test .lt x 1 then 0 else x-1) cursor

theorem node_stable (A : Layout) {m old : Memory W}
    (cursor : m ((A.nodePorts.cursor:Word W)).val=old ((A.nodePorts.cursor:Word W)).val) :
    nodeWord A m=nodeWord A old := by
  exact congrArg (fun u : Word W => (A.nodePorts.nodes:Word W)+8*u) (id_stable A cursor)

theorem privatePage_stable (A : Layout) {m old : Memory W}
    (cursor : m ((A.nodePorts.cursor:Word W)).val=old ((A.nodePorts.cursor:Word W)).val) (j : ℕ) :
    (selected A m).privatePage j=(selected A old).privatePage j := by
  let sector := HistoryScratch.sector A.party.motifs A.party.parties ⟨A.party.motif+2,A.party.party+2,2,j⟩
  exact congrArg (fun u : Word W => (A.party.arena:Word W)+(u*(A.party.V:Word W)+
    (sector:Word W))*(A.party.V:Word W)) (id_stable A cursor)

/-- The header scanner reads the saved node pointer and the two words of the
party mask test. If the ordinal is outside the row count, the incident's
six-word array need not be present. -/
structure MaskRoom (A : Layout) (input : Memory W) (lo hi : ℕ) : Prop where
  cursor : ((A.nodePorts.cursor:Word W)).val<lo ∨ hi≤((A.nodePorts.cursor:Word W)).val
  node : (nodeWord A input+5).val<lo ∨ hi≤(nodeWord A input+5).val
  count : ((selected A input).kernel+3).val<lo ∨ hi≤((selected A input).kernel+3).val
  incident : (A.party.motif:Word W)<wordAt input (selected A input).kernel 3 →
    ((selected A input).kernel+4).val<lo ∨ hi≤((selected A input).kernel+4).val
  mask : (A.party.motif:Word W)<wordAt input (selected A input).kernel 3 →
    ((selected A input).incident+5).val<lo ∨ hi≤((selected A input).incident+5).val

theorem MaskRoom.active {A : Layout} {old m : Memory W} {lo hi : ℕ} (r : MaskRoom A old lo hi)
    (frame : DescriptorScan.agreesOutside lo hi m old) : partyActive A m ↔ partyActive A old := by
  have cursor:=frame _ r.cursor
  have kernel : (selected A m).kernel=(selected A old).kernel := by
    change m (nodeWord A m+5).val=_
    rw [node_stable A cursor,frame _ r.node]
    rfl
  have count : wordAt m (selected A m).kernel 3=wordAt old (selected A old).kernel 3 := by
    unfold wordAt
    rw [kernel]
    exact frame _ r.count
  unfold partyActive
  dsimp only
  rw [count]
  by_cases live : (A.party.motif:Word W)<wordAt old (selected A old).kernel 3
  · have incident : (selected A m).incident=(selected A old).incident := by
      change m ((selected A m).kernel+4).val+(6*A.party.motif:ℕ)=_
      rw [kernel,frame _ (r.incident live)]
      rfl
    have mask : wordAt m (selected A m).incident 5=wordAt old (selected A old).incident 5 := by
      unfold wordAt
      rw [incident]
      exact frame _ (r.mask live)
    rw [mask]
  · simp only [live,false_and]

/-- The five scalar words selecting a shape and a physical party table. -/
theorem selected_rows_same (A : Layout) {input m : Memory W}
    (cursor : m ((A.nodePorts.cursor:Word W)).val=input ((A.nodePorts.cursor:Word W)).val)
    (node : m (nodeWord A input+5).val=input (nodeWord A input+5).val)
    (kernel : m ((selected A input).kernel+4).val=input ((selected A input).kernel+4).val)
    (shape : m ((selected A input).incident+2).val=input ((selected A input).incident+2).val) :
    (selected A m).incident=(selected A input).incident ∧
      (selected A m).kindPage=(selected A input).kindPage ∧ (selected A m).portPage=(selected A input).portPage := by
  have ker : (selected A m).kernel=(selected A input).kernel := by
    change m (nodeWord A m+5).val=_
    rw [node_stable A cursor,node]
    rfl
  have inc : (selected A m).incident=(selected A input).incident := by
    change m ((selected A m).kernel+4).val+(6*A.party.motif:ℕ)=_
    rw [ker,kernel]
    rfl
  have sh : wordAt m (selected A m).incident 2=wordAt input (selected A input).incident 2 := by
    unfold wordAt
    rw [inc]
    exact shape
  refine ⟨inc,?_,?_⟩
  · change (A.party.kinds:Word W)+7*(wordAt m (selected A m).incident 2*(A.party.parties:Word W)+_)=_
    rw [sh];rfl
  · change (A.catalogue:Word W)+(_ :Word W)*(wordAt m (selected A m).incident 2*(A.party.parties:Word W)+_)=_
    rw [sh];rfl

/-- The geometry, payload and tile widths all vanish off the actual party mask. -/
theorem inactive_width (A : Layout) (m : Memory W) (off : ¬partyActive A m) (q : Bool) (j : ℕ) :
    physicalWidth A m q j=0 := by
  simp only [physicalWidth,portActive,off,false_and,ite_false]

theorem inactive_header (A : Layout) (m : Memory W) (off : ¬partyActive A m) :
    headerWords A m=numericHeaderWords A (fun _ _=>0) (fun _=>0) (fun _=>0)
      ((selected A m).privatePage 2) 0 := by
  have width : physicalWidth A m=fun _ _=>0 := funext (fun q=>funext (inactive_width A m off q))
  have payload : payloadWidth A m=fun _=>0 := by
    funext j
    simp [payloadWidth,width,off,cutWord]
  have tile : tileWidth A m=fun _=>0 := by
    funext j
    simp [tileWidth,portActive,off]
  simp [headerWords,width,payload,tile,partyMapCount,off]

theorem inactive_stable (A : Layout) (input m : Memory W)
    (off : ¬partyActive A input) (inactive : ¬partyActive A m)
    (base : (selected A m).privatePage 2=(selected A input).privatePage 2) :
    headerWords A m=headerWords A input := by
  rw [inactive_header A m inactive,inactive_header A input off,base]

/-- The loaded addresses of the selected branch of a numeric formula in a fixed memory. -/
def protectedFormula {n : ℕ} (save : ℕ→Prop) (input : Memory W) (vs : Fin n→Word W) :
    Formula n→Prop
  | .reg _ | .lit _ | .param _ => True
  | .op _ a b | .cut a b => protectedFormula save input vs a ∧ protectedFormula save input vs b
  | .load a => protectedFormula save input vs a ∧ save (a.value (fun _=>0) input vs).val
  | .select test a b yes no =>
    protectedFormula save input vs a ∧ protectedFormula save input vs b ∧
    (if test.test (a.value (fun _=>0) input vs) (b.value (fun _=>0) input vs)
      then protectedFormula save input vs yes else protectedFormula save input vs no)

private theorem protectedFormula.value {n : ℕ} {save : ℕ→Prop} {m input : Memory W} (vs : Fin n→Word W)
    (same : ∀a,save a → m a=input a) (t : Formula n) (ok : protectedFormula save input vs t) :
    t.value (fun _=>0) m vs=t.value (fun _=>0) input vs := by
  induction t with
  | reg _ | lit _ | param _ => rfl
  | op b x y ix iy => simp only [Formula.value,ix ok.1,iy ok.2]
  | cut x y ix iy => simp only [Formula.value,ix ok.1,iy ok.2]
  | load x ix => simpa only [Formula.value,ix ok.1] using same _ ok.2
  | select cmp x y yes no ix iy iy' ino =>
    simp only [Formula.value,ix ok.1,iy ok.2.1]
    have pick:=ok.2.2
    split
    next taken => exact iy' (by simpa only [ite_eq_left taken] using pick)
    next skipped => exact ino (by simpa only [ite_eq_right skipped] using pick)

section RefreshWidthBounds
open Diagonal.RefreshParty Diagonal.RefreshDemandRows MotifRows
variable (saved : ℕ→Prop) (input : Memory W) (vs : Fin 7→Word W)
local notation "ok" => protectedFormula saved input vs
local notation "VW" => Formula.value (fun _=>0) input vs

private theorem formulaSelect (cmp : Comparison) (x y yes no : Formula 7)
    (hx : ok x) (hy : ok y) (ht : ok yes) (hf : ok no) : ok (.select cmp x y yes no) := by
  refine ⟨hx,hy,?_⟩
  split <;> assumption

private theorem archivedField (k : ℕ) (hk : saved (vs 0+(k:Word W)).val) :
    ok (stageField k) := ⟨⟨trivial,trivial⟩,hk⟩

private theorem wordOK (m : ℕ) (rest base slot port lane : Formula 7)
    (hr : ok rest) (hb : ok base) (hs : ok slot) (hp : ok port) (hl : ok lane) :
    ok (wordAddress m rest base slot port lane) :=
  ⟨⟨⟨⟨hb,trivial⟩,hs⟩,⟨trivial,hr⟩⟩,⟨hp,⟨trivial,hl⟩⟩⟩

/-- The two sparse directions read one stage pointer and the two possible
successor half-width rows in the persistent four-word half array. -/
theorem protected_refresh_supply (m h pad : ℕ) (head : saved (vs 0+(40:Word W)).val)
    (half : ∀side:Bool, let other : Formula 7:=.op .mod (.reg 4) (.lit h)
      let slot:=plus (.lit (1+(if side then 1+h+pad else 0))) other
      let row:=plus (.op .mul (.reg 1) (.lit (2*(1+h+pad)))) slot
      saved (VW (plus (stageField 40) (plus (.op .mul row (.lit 4)) (.lit 2)))).val) :
    ok (width m h pad true) := by
  have h40:=archivedField saved input vs 40 head
  have side (b : Bool) : ok (sparseWidth (1+h+pad) b (.op .mod (.reg 4) (.lit h))) := by
    refine ⟨⟨h40,?_⟩,half b⟩
    exact ⟨⟨⟨⟨trivial,trivial⟩,⟨trivial,⟨trivial,trivial⟩⟩⟩,trivial⟩,trivial⟩
  exact formulaSelect saved input vs _ _ _ _ _ trivial trivial (side false) (side true)

/-- Explicit protected intervals for a refresh demand lookup. The reverse edge
reads its four source-slot columns, and each direction then reads its old width. -/
theorem protected_refresh_demand (m h pad : ℕ)
    (stage : ∀ k∈([8,9,10,11,12]:List ℕ),saved (vs 0+(k:Word W)).val)
    (incident : saved (vs 2).val)
    (columns : ∀side:Bool, let other : Formula 7:=.op .mod (.reg 4) (.lit m)
      let slot:=if side then .reg 3 else other
      let row:=plus (.op .mul (.op .div (.load (.reg 2)) (stageField 8)) (.lit m)) slot
      ∀c∈[inputs.sourceBase,inputs.sourceSlot,inputs.portShift,inputs.laneShift],
        saved (VW (plus c row)).val)
    (widthCell : ∀ back side:Bool,let other : Formula 7:=.op .mod (.reg 4) (.lit m)
      saved (VW (coordinates m inputs (stageField 8) (.load (.reg 2)) back
        (if side then other else .reg 3) (if side then .reg 3 else other))).val) :
    ok (width m h pad false) := by
  have h8:=archivedField saved input vs 8 (stage 8 (by simp))
  have h9:=archivedField saved input vs 9 (stage 9 (by simp))
  have h10:=archivedField saved input vs 10 (stage 10 (by simp))
  have h11:=archivedField saved input vs 11 (stage 11 (by simp))
  have h12:=archivedField saved input vs 12 (stage 12 (by simp))
  let other : Formula 7 := .op .mod (.reg 4) (.lit m)
  have ho : ok other := ⟨trivial,trivial⟩
  have hc : ok (.load (.reg 2)) := ⟨trivial,incident⟩
  have nominal (back side : Bool) : ok (denseWidth m back side other) := by
    let port := if side then other else .reg 3
    let slot := if side then .reg 3 else other
    let row := plus (.op .mul (.op .div (.load (.reg 2)) (stageField 8)) (.lit m)) slot
    have op : ok port := by cases side <;> first | exact ho | trivial
    have os : ok slot := by cases side <;> first | exact ho | trivial
    have rr : ok row := ⟨⟨⟨hc,h8⟩,trivial⟩,os⟩
    have atCol (col : Formula 7) (allowed : col∈[inputs.sourceBase,inputs.sourceSlot,inputs.portShift,inputs.laneShift])
        (access : ok col) : ok (readColumn col row) := ⟨⟨access,rr⟩,columns side col allowed⟩
    refine ⟨?_,widthCell back side⟩
    change ok (coordinates m inputs (stageField 8) (.load (.reg 2)) back port slot)
    unfold coordinates
    refine ⟨h9,?_⟩
    cases back with
    | false => exact wordOK saved input vs _ _ _ _ _ _ h8 ⟨hc,h8⟩ os op ⟨hc,h8⟩
    | true =>
      apply wordOK saved input vs _ _ _ _ _ _ h8
      · exact atCol _ (by simp) ⟨h10,⟨h11,trivial⟩⟩
      · exact atCol _ (by simp) ⟨h10,⟨h11,trivial⟩⟩
      · exact ⟨op,atCol _ (by simp) ⟨h12,⟨h11,trivial⟩⟩⟩
      · exact ⟨⟨hc,h8⟩,atCol _ (by simp) ⟨h12,⟨h11,trivial⟩⟩⟩
  apply formulaSelect saved input vs .lt (.reg 4) (.lit m) _ _ trivial trivial (nominal false false)
  apply formulaSelect saved input vs .lt (.reg 4) (.lit (2*m)) _ _ trivial trivial (nominal false true)
  exact formulaSelect saved input vs .lt (.reg 4) (.lit (3*m)) _ _ trivial trivial
    (nominal true false) (nominal true true)

end RefreshWidthBounds

/-- Stage data needed by one enabled port. These are all addresses in the input memory,
including the addressed physical-width cell or the selected graph-width formula. -/
def widthReads (A : Layout) (m : Memory W) (q : Bool) (i : ℕ) (save : ℕ→Prop) : Prop :=
  let R:=selected A m
  let stage:=m R.kernel.val
  let code:=portCode A m q i
  let row:=BinaryOp.eval .div (cutWord (wordAt m R.incident 1) (wordAt m stage 1)) (A.histogramStride:Word W)
  save R.kernel.val ∧ save (R.portPage+((if q then HistoryPortCatalogue.supplyBase A.demandCap+i
    else HistoryPortCatalogue.demandBase+2*i : ℕ):Word W)).val ∧
  match A.mode with
  | .shrink _ =>
    save (R.incident+1).val ∧ save (stage+1).val ∧
    save (stage+(if q then 3 else 8 : Word W)).val ∧
    save (wordAt m stage (if q then 3 else 8)+((if q then 8 else 2 : Word W)*row+code)).val
  | .refresh n d pad => save (R.kernel+1).val ∧
    protectedFormula save m (refreshWidthRegisters A m q i) (Diagonal.RefreshParty.width n d pad q)

/-- A shrink lookup stays in its chosen physical width row. The required persistent
addresses are one node pointer, one catalogue code, three header cells, and that row. -/
theorem widthReads.shrink (A : Layout) (input : Memory W) (S : Graph.Stage) (q : Bool) (i row code hist tab : ℕ)
    (saved : ℕ→Prop) (mode : A.mode=.shrink S) (stride : 0<A.histogramStride)
    (strideFit : A.histogramStride<2^W)
    (histRow : (wordAt input (selected A input).incident 1).val=hist+row*A.histogramStride)
    (histBase : (wordAt input (input (selected A input).kernel.val) 1).val=hist)
    (port : portCode A input q i=(code:Word W))
    (bank : wordAt input (input (selected A input).kernel.val) (if q then 3 else 8)=(tab:Word W))
    (space : tab+((if q then 8 else 2)*row+code)<2^W)
    (kernel : saved (selected A input).kernel.val)
    (catalogue : saved ((selected A input).portPage+((if q then HistoryPortCatalogue.supplyBase A.demandCap+i
      else HistoryPortCatalogue.demandBase+2*i : ℕ):Word W)).val)
    (incident : saved ((selected A input).incident+1).val)
    (counts : saved (input (selected A input).kernel.val+1).val)
    (table : saved (input (selected A input).kernel.val+(if q then 3 else 8 : Word W)).val)
    (cell : saved (tab+((if q then 8 else 2)*row+code))) :
    widthReads A input q i saved := by
  have fit : row*A.histogramStride<2^W := by have := (wordAt input (selected A input).incident 1).isLt;omega
  have sub:=difference _ _ _ _ histBase histRow
  have quo:=WordQuotients.div_at (row*A.histogramStride) A.histogramStride fit strideFit
  rw [Nat.mul_div_cancel _ stride] at quo
  unfold widthReads
  rw [mode]
  refine ⟨kernel,catalogue,incident,counts,table,?_⟩
  rw [sub,quo,port,bank]
  cases q <;> simp only [Bool.false_eq_true,ite_false,ite_true] at * <;>
    rw [←Nat.cast_ofNat (R:=Word W),←Nat.cast_mul,←Nat.cast_add,←Nat.cast_add,Fin.val_cast_of_lt space] <;>
    exact cell

private theorem widthReads.stable {A : Layout} {input m : Memory W} (q : Bool) (i : ℕ) {save : ℕ→Prop}
    (same : ∀a,save a → m a=input a) (ok : widthReads A input q i save)
    (kernel : (selected A m).kernel=(selected A input).kernel)
    (inc : (selected A m).incident=(selected A input).incident)
    (page : (selected A m).portPage=(selected A input).portPage)
    (live : portActive A m q i) (active : portActive A input q i) :
    physicalWidth A m q i=physicalWidth A input q i := by
  have stage : m (selected A m).kernel.val=input (selected A input).kernel.val := by
    rw [kernel];exact same _ ok.1
  have code : portCode A m q i=portCode A input q i := by
    unfold portCode wordAt
    rw [page];exact same _ ok.2.1
  have rd:=ok.2.2
  unfold physicalWidth
  rw [ite_eq_left live,ite_eq_left active]
  cases mode : A.mode with
  | shrink S =>
    rw [mode] at rd
    have a : wordAt m (selected A m).incident 1=wordAt input (selected A input).incident 1 := by
      unfold wordAt;rw [inc];exact same _ rd.1
    have b : wordAt m (m (selected A m).kernel.val) 1=wordAt input (input (selected A input).kernel.val) 1 := by
      unfold wordAt;rw [stage];exact same _ rd.2.1
    have c : wordAt m (m (selected A m).kernel.val) (if q then 3 else 8)=
        wordAt input (input (selected A input).kernel.val) (if q then 3 else 8) := by
      unfold wordAt;rw [stage];cases q <;> exact same _ rd.2.2.1
    rw [a,b,c,code]
    exact same _ rd.2.2.2
  | refresh n d pad =>
    rw [mode] at rd
    have site : wordAt m (selected A m).kernel 1=wordAt input (selected A input).kernel 1 := by
      unfold wordAt;rw [kernel];exact same _ rd.1
    rw [stage,site,inc,code]
    exact protectedFormula.value (refreshWidthRegisters A input q i) same _ rd.2

private theorem header_congr (A : Layout) {w u : Bool→ℕ→Word W} {a b c d : ℕ→Word W} (x y : Word W)
    (width : ∀q j,j<(if q then A.supplyCap else A.demandCap) → w q j=u q j)
    (payload : ∀j,j<A.supplyCap → a j=b j) (tile : ∀j,j<A.demandCap → c j=d j) :
    numericHeaderWords A w a c x y=numericHeaderWords A u b d x y := by
  have side (q : Bool) :
      (List.range (if q then A.supplyCap else A.demandCap)).flatMap
        (fun j=>[(srcBase A q j:Word W),w q j])=
      (List.range (if q then A.supplyCap else A.demandCap)).flatMap
        (fun j=>[(srcBase A q j:Word W),u q j]) := by
    apply List.flatMap_congr
    intro j hj
    rw [width q j (List.mem_range.mp hj)]
  have output : (List.range A.supplyCap).flatMap (fun j=>[(srcBase A true j:Word W),a j])=
      (List.range A.supplyCap).flatMap (fun j=>[(srcBase A true j:Word W),b j]) := by
    apply List.flatMap_congr
    intro j hj
    rw [payload j (List.mem_range.mp hj)]
  have input : (List.range A.demandCap).flatMap (fun j=>[(srcBase A false j:Word W),w false j,c j])=
      (List.range A.demandCap).flatMap (fun j=>[(srcBase A false j:Word W),u false j,d j]) := by
    apply List.flatMap_congr
    intro j hj
    rw [width false j (List.mem_range.mp hj),tile j (List.mem_range.mp hj)]
  have demand := side false
  have supply := side true
  simp only [Bool.false_eq_true,ite_false,ite_true] at demand supply
  dsimp only [numericHeaderWords]
  rw [demand,supply,output,input]


/-- The read-only archive and S38 catalogue cells needed by an active header.
The mutable cursor and the party's private S12 count word are handled separately. -/
structure ArchiveHeader (A : Layout) (input : Memory W) (saved : ℕ→Prop) : Prop where
  node : saved (nodeWord A input+5).val
  count : saved ((selected A input).kernel+3).val
  rows : saved ((selected A input).kernel+4).val
  shape : saved ((selected A input).incident+2).val
  mask : saved ((selected A input).incident+5).val
  copies : saved ((selected A input).incident+3).val
  selector : saved ((selected A input).kindPage+2).val
  length : ∀q:Bool,saved ((selected A input).portPage+(q.toNat:Word W)).val
  digit : ∀i,i<A.demandCap → portActive A input false i →
    saved ((selected A input).portPage+((HistoryPortCatalogue.demandBase+2*i+1:ℕ):Word W)).val
  width : ∀q i,i<(if q then A.supplyCap else A.demandCap) → portActive A input q i →
    widthReads A input q i saved

/-- The selected header's only nonarchive reads are the chronology cursor and one
count in its private party result. The saved ranges may lie on either side of S17. -/
theorem HeaderFootprint.of_archive (A : Layout) (input : Memory W) (saved : ℕ→Prop)
    (bounds : ArchiveHeader A input saved)
    (apart : ∀a,saved a → a<A.temp ∨ A.temp+(fields (W:=W) A).length≤a)
    (cursor : (A.nodePorts.cursor:Word W).val<A.temp ∨ A.temp+(fields (W:=W) A).length≤(A.nodePorts.cursor:Word W).val)
    (pair : let a:=((selected A input).privatePage 1+1).val
      a<A.temp ∨ A.temp+(fields (W:=W) A).length≤a) :
    HeaderFootprint A input A.temp (A.temp+(fields (W:=W) A).length) := by
  constructor
  intro m frame
  have same (addr : ℕ) (stored : saved addr) : m addr=input addr := frame _ (apart addr stored)
  have ctr:=frame _ cursor
  have ker : (selected A m).kernel=(selected A input).kernel := by
    change m (nodeWord A m+5).val=_
    rw [node_stable A ctr]
    exact same _ bounds.node
  have sel:=selected_rows_same A ctr (same _ bounds.node) (same _ bounds.rows) (same _ bounds.shape)
  have mask : MaskRoom A input A.temp (A.temp+(fields (W:=W) A).length) := ⟨cursor,
    apart _ bounds.node,apart _ bounds.count,
    fun _=>apart _ bounds.rows,fun _=>apart _ bounds.mask⟩
  have active:=mask.active frame
  have port (q : Bool) (i : ℕ) : portActive A m q i ↔ portActive A input q i := by
    unfold portActive
    rw [active]
    unfold wordAt
    rw [sel.2.2,same _ (bounds.length q)]
  have wide (q : Bool) (i : ℕ) (hi:i<(if q then A.supplyCap else A.demandCap)) :
      physicalWidth A m q i=physicalWidth A input q i := by
    by_cases use : portActive A input q i
    · exact widthReads.stable q i same (bounds.width q i hi use) ker sel.1 sel.2.2 ((port q i).2 use) use
    · simp only [physicalWidth,ite_eq_right use,ite_eq_right (fun act=>use ((port q i).1 act))]
  have copies : wordAt m (selected A m).incident 3=wordAt input (selected A input).incident 3 := by
    unfold wordAt;rw [sel.1];exact same _ bounds.copies
  have bits : wordAt m (selected A m).kindPage 2=wordAt input (selected A input).kindPage 2 := by
    unfold wordAt;rw [sel.2.1];exact same _ bounds.selector
  have count : partyMapCount A m=partyMapCount A input := by
    unfold partyMapCount wordAt
    rw [active,privatePage_stable A ctr 1]
    simp only [Nat.cast_one]
    rw [frame _ pair]
  unfold headerWords
  rw [privatePage_stable A ctr 2,count]
  apply header_congr A _ _ wide
  · intro i hi
    dsimp only [payloadWidth]
    rw [active,copies,bits,wide true i hi]
  · intro i hi
    unfold tileWidth
    rw [propext (port false i)]
    split
    · unfold wordAt
      rw [sel.2.2]
      exact same _ (bounds.digit i hi ‹_›)
    · rfl



end
end ThreeFlat.RAM.HistoryGatherBody

end OAI
