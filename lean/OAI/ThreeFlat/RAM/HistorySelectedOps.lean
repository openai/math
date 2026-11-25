import OAI.ThreeFlat.RAM.HistorySelectedAuxSize
import OAI.ThreeFlat.RAM.HistoryCommandParameter
import OAI.ThreeFlat.RAM.HistoryCommandSweep
import OAI.ThreeFlat.RAM.HistoryOperandScan
import OAI.ThreeFlat.RAM.HistoryLeafROM
import OAI.ThreeFlat.RAM.HistoryFinalCopy
import OAI.ThreeFlat.RAM.HistoryGeometryPointer
import OAI.ThreeFlat.RAM.HistoryBatchTape
import OAI.ThreeFlat.RAM.HistoryBoundedJoin
import OAI.ThreeFlat.RAM.HistoryTerminalTape
import OAI.ThreeFlat.RAM.HistoryPartyHeader
import OAI.ThreeFlat.RAM.HistoryStageRoot
import OAI.ThreeFlat.RAM.HistoryPortMap
import OAI.ThreeFlat.RAM.HistoryPairSeeds

namespace OAI
/-! # Fixed opcodes for each selected history node's local expansion -/

namespace ThreeFlat.RAM.HistorySelectedOps

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr HistoryCommandParameter
open HistoryOperandScan
open scoped Fin.CommRing

noncomputable section

variable {w k : ℕ}

/-- A control record begins with [operandBase,destination,opcode]. Its seventh
word is the past-the-end output address, shared with the command controller. -/
def opcode (control : Fin k) : Term w k 1 :=
  (Term.binary .add (Term.parameter control).load (.literal 2)).load

def choice (control : Fin k) : ℕ → List (Term w k 1) → Term w k 1
  | _, [] => .literal 0
  | j, e::es => Term.select .eq (opcode control) (.literal (j:Word w)) e (choice control (j+1) es)

theorem choice_at (control : Fin k) (data : Fin k → Word w) (mem : Memory w) (vs : Fin 1 → Word w)
    (j : ℕ) (es : List (Term w k 1)) (i : Fin es.length) (room : j+es.length≤2^w)
    (tag : (mem (mem (data control).val+2).val).val=j+i.val) :
    (choice control j es).eval data mem vs=(es.get i).eval data mem vs := by
  induction es generalizing j with
  | nil => exact Fin.elim0 i
  | cons e es ih =>
    revert tag
    refine Fin.cases ?_ (fun i => ?_) i
    · intro tag
      have word : mem (mem (data control).val+2).val=(j:Word w) := by
        apply Fin.ext
        simpa only [Fin.val_natCast,Nat.mod_eq_of_lt (show j<2^w by simp at room; omega),Fin.val_zero,Nat.add_zero] using tag
      simp [choice,opcode,BinaryOp.eval,DescriptorExpr.Comparison.test,word]
    · intro tag
      have small : j<2^w := by simp at room; omega
      have different : mem (mem (data control).val+2).val≠(j:Word w) := by
        intro h
        have t := congrArg Fin.val h
        simp only [Fin.val_natCast,Nat.mod_eq_of_lt small] at t
        rw [tag] at t
        simp only [Fin.val_succ] at t
        omega
      simp only [choice,Term.eval_select,Term.eval_literal,opcode,Term.eval_load,Term.eval_binary,
        Term.eval_parameter,BinaryOp.eval,DescriptorExpr.Comparison.test,beq_iff_eq,
        different,ite_false]
      exact ih (j+1) i (by simp at room; omega) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tag)

def leafArg (k : ℕ) (control : Fin (k+1)) (i : Fin (k+1)) : Term w (k+1) 0 :=
  if i=Fin.last k then operandBlock control else .parameter i

/-- One fixed table assembled over the finite degree/grid types permitted by
the compressor. Geometry expressions are compiled separately for each type;
the local arrays and copy counts of a stage are exclusively runtime data. -/
def core (initial : Term w k 4) : List (Term w (k+1) 1) :=
  let ctrl := Fin.last k
  let arg1 (prog : Term w 1 1) := onlyBlock ctrl prog
  let indirectJoin := replace (fun _ : Fin 1 => (Term.parameter ctrl).load)
    (HistoryJoinScan.term (w:=w) (0 : Fin 1))
  let finalOp := program (HistoryFinalCopy.term (w:=w) (k:=1)) (0 : Fin 1) 1 ![.row,.header 2,.header 3,.header 4]
  [replace (leafArg k ctrl) (HistoryLeafDispatch.mountedLeaves initial),indirectJoin,
    arg1 (batches w),arg1 (party w),arg1 (motif w),arg1 finalOp]

/-- For each old or new port of either kind of real geometric step the same
scan advances along the requested bit. Its other twelve operands are the
selected node's bounded-arity addresses and indices. -/
def geometry (q : Term w 1 13) (ctrl : Fin k) : Term w k 1 :=
  onlyBlock ctrl (program q (0 : Fin 1) 1 ![.header 2,.header 3,.header 4,.header 5,
    .header 6,.row,.header 7,.header 8,.header 9,.header 10,.header 11,.header 12,.header 13])

def rows (initial : Term w k 4) (shapes : List (Term w 1 13)) :=
  choice (Fin.last k) 0 (core initial ++ (auxiliary w).map (onlyBlock (Fin.last k)) ++ shapes.map (fun q => geometry q (Fin.last k)))

def block (initial : Term w k 4) (shapes : List (Term w 1 13)) :=
  HistoryCommandSweep.block (rows initial shapes) (Fin.last k)

/-- The only geometry opcodes come from the finite compressor stage types.
Each stage has a demand lookup followed by a supply lookup. -/
inductive Geometry
  | shrink (stage : Diagonal.CompressorPacking.Native.Graph.Stage)
  | refresh (ports degree padding : ℕ)
  | localJoin (childBound : ℕ)
  | terminal
  | partyHeader
  | stageRoot (cap : ℕ) (bank : HistoryStageRoot.Bank)

def Geometry.term (W : ℕ) (supply : Bool) : Geometry → Term W 1 13
  | .shrink stage => HistoryGeometryPointer.shrink W stage supply
  | .refresh m h pad => HistoryGeometryPointer.refresh W m h pad supply
  | .localJoin cap => HistoryBoundedJoin.program W cap supply
  | .terminal => HistoryTerminalTape.program W supply
  | .partyHeader => HistoryPartyHeader.program W supply
  | .stageRoot cap bank => HistoryStageRoot.program W cap bank

theorem Geometry.size (g : Geometry) (W W' : ℕ) (supply : Bool) :
    (g.term W supply).binds=(g.term W' supply).binds := by
  cases g with
  | shrink stage => exact HistoryGeometryPointer.shrink_size ..
  | refresh m h pad => exact HistoryGeometryPointer.refresh_size ..
  | localJoin cap => exact HistoryBoundedJoin.program_size ..
  | terminal => exact HistoryTerminalTape.program_size ..
  | partyHeader => exact HistoryPartyHeader.program_size ..
  | stageRoot cap bank => exact HistoryStageRoot.program_size ..

def geometryList (W : ℕ) (types : List Geometry) :=
  types.flatMap (fun g => [g.term W false,g.term W true])

def selectedBlock (W : ℕ) (types : List Geometry) := block (TraceEndpointROM.fixed W) (geometryList W types)

theorem choice_size (control : Fin k) (j : ℕ) (es : List (Term w k 1)) :
    (choice control j es).binds=1+es.length*7+(es.map Term.binds).sum := by
  induction es generalizing j with
  | nil => simp [choice,Term.literal,Term.binds]
  | cons e es ih =>
    simp only [choice,Term.select,opcode,Term.load,Term.binary,Term.parameter,
      Term.literal,Term.binds_letThen,Term.binds_rename,Term.binds,ih,List.length_cons,List.map_cons,List.sum_cons]
    omega

private theorem leafArg_cost (k : ℕ) (ctrl : Fin (k+1)) (i : Fin (k+1)) :
    (leafArg (w:=w) k ctrl i).binds≤3 := by
  unfold leafArg
  split
  · exact le_refl 3
  · exact (by decide : 1 ≤ 3)

private theorem geometry_cost (q : Term w 1 13) (ctrl : Fin k) :
    (geometry q ctrl).binds≤3*(q.binds+91) := by
  have m := onlyBlock_binds ctrl (program q (0 : Fin 1) 1 ![.header 2,.header 3,.header 4,.header 5,
    .header 6,.row,.header 7,.header 8,.header 9,.header 10,.header 11,.header 12,.header 13])
  have b := binds_le q (0 : Fin 1) 1 ![.header 2,.header 3,.header 4,.header 5,.header 6,.row,
    .header 7,.header 8,.header 9,.header 10,.header 11,.header 12,.header 13]
  exact m.trans (by omega)

private theorem core_budget (extra : ℕ) :
    (1000234+extra+160)*3 + (125*2 + (298*3 + (1070*3 + (363*3 + ((18+7*4)*3+0))))) ≤
      3010000+3*extra := by omega

theorem core_size (initial : Term w k 4) (extra : ℕ) (small : initial.binds≤1000234+extra) :
    ((core initial).map Term.binds).sum≤3010000+3*extra := by
  let ctrl := Fin.last k
  have leaf := binds_replace (leafArg k ctrl) (HistoryLeafDispatch.mountedLeaves initial) 3
    (by decide) (leafArg_cost k ctrl)
  have raw := HistoryLeafDispatch.mountedLeaves_binds initial
  have move := binds_replace (fun _ : Fin 1 => ((Term.parameter ctrl).load : Term w (k+1) 0))
    (HistoryJoinScan.term (w:=w) (0:Fin 1)) 2 (by decide) (fun _ => le_refl 2)
  rw [HistoryJoinScan.term_binds] at move
  have sizes := bounds w
  have a := onlyBlock_binds ctrl (batches w)
  have b := onlyBlock_binds ctrl (party w)
  have c := onlyBlock_binds ctrl (motif w)
  let src := program (HistoryFinalCopy.term (w:=w) (k:=1)) (0 : Fin 1) 1 ![.row,.header 2,.header 3,.header 4]
  have last := onlyBlock_binds ctrl src
  have z : src.binds ≤ 18+7*4 := (binds_le ..).trans (Nat.add_le_add_right HistoryFinalCopy.term_binds _)
  have first := leaf.trans (Nat.mul_le_mul_right 3 (raw.trans (Nat.add_le_add_right small 160)))
  have batchesBound := a.trans (Nat.mul_le_mul_right 3 sizes.1)
  have partyBound := b.trans (Nat.mul_le_mul_right 3 sizes.2.1)
  have motifBound := c.trans (Nat.mul_le_mul_right 3 sizes.2.2)
  have finalBound := last.trans (Nat.mul_le_mul_right 3 z)
  exact (Nat.add_le_add first (Nat.add_le_add move (Nat.add_le_add batchesBound
    (Nat.add_le_add partyBound (Nat.add_le_add motifBound (Nat.add_le_add finalBound (le_refl 0))))))).trans
    (core_budget extra)

def tariff (types : List Geometry) := 3010150 + 3*((auxiliary 1).map Term.binds).sum + (types.map (fun g => 14+3*(182+
  (g.term 1 false).binds+(g.term 1 true).binds))).sum

private theorem sum_mount (ctrl : Fin k) (es : List (Term w 1 1)) :
    ((es.map (onlyBlock ctrl)).map Term.binds).sum≤3*(es.map Term.binds).sum := by
  induction es with
  | nil => simp
  | cons x xs ih =>
    have b := onlyBlock_binds ctrl x
    simp only [List.map_cons,List.sum_cons]
    omega

theorem rows_size_add (W : ℕ) (A : Term W k 4) (extra : ℕ) (small : A.binds ≤ 1000234+extra) (types : List Geometry) :
    (rows A (geometryList W types)).binds ≤ tariff types+3*extra := by
  let ctrl := Fin.last k
  have start := core_size A extra small
  have bound : (geometryList W types).length*7+
      ((geometryList W types).map (fun q => (geometry q ctrl).binds)).sum ≤
      (types.map (fun g => 14+3*(182+(g.term 1 false).binds+(g.term 1 true).binds))).sum := by
    induction types with
    | nil => simp [geometryList]
    | cons x xs ih =>
      have l := geometry_cost (x.term W false) ctrl
      have r := geometry_cost (x.term W true) ctrl
      rw [x.size W 1 false] at l
      rw [x.size W 1 true] at r
      simp only [geometryList,List.flatMap_cons,List.cons_append,List.nil_append,List.length_cons,
        List.map_cons,List.sum_cons] at ih ⊢
      omega
  have count : (core A).length=6 := rfl
  have count₂ : (auxiliary W).length=6 := rfl
  have aux := sum_mount ctrl (auxiliary W)
  rw [aux_size W] at aux
  simp only [List.map_map,Function.comp_def,ctrl] at aux bound
  simp only [rows,choice_size,List.length_append,List.length_map,count,count₂,List.map_append,
    List.sum_append,List.map_map,Function.comp_def,tariff]
  omega

theorem rows_size_of (W : ℕ) (A : Term W k 4) (small : A.binds ≤ 1000234) (types : List Geometry) :
    (rows A (geometryList W types)).binds ≤ tariff types := by
  simpa only [Nat.mul_zero,Nat.add_zero] using rows_size_add W A 0 small types

end
theorem rows_size (W : ℕ) (types : List Geometry) :
    (rows (TraceEndpointROM.fixed W) (geometryList W types)).binds ≤ tariff types :=
  rows_size_of W (TraceEndpointROM.fixed W) (TraceEndpointROM.fixed_binds W) types


end ThreeFlat.RAM.HistorySelectedOps

end OAI
