import OAI.ThreeFlat.RAM.HistoryPartyCatalogueData
import OAI.ThreeFlat.RAM.HistoryBatchTape
import OAI.ThreeFlat.RAM.HistoryCompactorCounts

namespace OAI
/-! # Native construction of both regular batch headers at a selected party -/

namespace ThreeFlat.RAM.HistoryPartyHeader

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalPinsExpr HistoryBatchTape
open Diagonal.HistoryContraction.Tree
open scoped Fin.CommRing

/-- These operands are either selected scratch cursors, a live six-word
motif, the `HistoryDyadic` output, or the immutable archive page bases. -/
structure Registers where
  arguments : ℕ
  streams : ℕ
  maps : ℕ
  incident : ℕ
  grid : ℕ
  dyadic : ℕ
  lutBase : ℕ
  lutStride : ℕ
  compBase : ℕ
  compStride : ℕ
  countBase : ℕ

def Registers.words (v : Registers) : Fin 11→ℕ :=
  ![v.arguments,v.streams,v.maps,v.incident,v.grid,v.dyadic,v.lutBase,v.lutStride,v.compBase,v.compStride,v.countBase]

def batch (A : Registers) (B : Kind) (m : ℕ→ℕ) (checks : Bool) : Header :=
  let copies := m (A.incident+3)
  let hist := m (A.incident+1)
  let exponent := m (A.dyadic+1)
  let N := m (A.dyadic+2)
  let sb := B.ports*B.codeBits
  let b := if checks then sb else B.tileHead
  let s := if checks then B.letters else B.ports
  let ar := if checks then sb+B.letters else B.tileHead+2*(B.ports*B.digit)
  let page := if checks then B.selectorPage else B.tilePage
  let lut := A.lutBase+A.lutStride*page
  let small := if checks then copies else copies*B.digit
  let cptr := A.countBase+2*exponent
  let left : BatchRows.Size := ⟨ar,m (lut+1),m lut⟩
  let right : BatchRows.Size := ⟨3*small,N*m cptr,N*m (cptr+1)⟩
  let bank := B.ports*(copies*B.digit)
  ⟨A.arguments,A.streams,A.maps,copies,s,left,right,if checks then copies*sb else copies*b+bank,
   if checks then copies*B.letters else 2*bank,checks,b,B.ports,B.digit,B.letters,hist,
   ![A.lutBase,A.lutStride,page],![N,small,A.compBase+A.compStride*exponent]⟩

private abbrev E := Formula 13
private def arg (j : ℕ) : E := .load (add (.reg 0) (.lit j))
private def grid (j : ℕ) : E := .load (add (arg 4) (.lit j))
private def read (a : E) (j : ℕ) : E := .load (add a (.lit j))

def formula (checks : Bool) : E :=
  let z := read (arg 3) 3
  let hist := read (arg 3) 1
  let exp := read (arg 5) 1
  let N := read (arg 5) 2
  let e := grid 0; let s := grid 1; let sb := mul e (grid 2)
  let b := if checks then sb else grid 3
  let d := grid 4
  let p := if checks then grid 6 else grid 5
  let len := if checks then z else mul z d
  let ar := if checks then add sb s else add (grid 3) (mul (.lit 2) (mul e d))
  let lut := add (arg 6) (mul (arg 7) p)
  let row := add (arg 10) (mul (.lit 2) exp)
  let bank := mul e (mul z d)
  HistoryBatchTape.choose (.reg 5) [arg 0,arg 1,arg 2,z,if checks then s else e,ar,read lut 1,.load lut,
    mul (.lit 3) len,mul N (.load row),mul N (read row 1),
    if checks then mul z sb else add (mul z b) bank,if checks then mul z s else mul (.lit 2) bank,
    .lit checks.toNat,b,e,d,s,hist,arg 6,arg 7,p,N,len,add (arg 8) (mul (arg 9) exp),.lit 0]

def program (W : ℕ) (checks : Bool) : Term W 1 13 := (formula checks).compile (fun _ => 0)

theorem program_size (W W' : ℕ) (checks : Bool) :
    (program W checks).binds=(program W' checks).binds := by simp [program,Formula.binds_compile]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem formula_word (W : ℕ) (A : Registers) (B : Kind) (checks : Bool)
    (base : ℕ) (pub : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin 13 → ℕ) (j : Fin 26)
    (args : ∀ i : Fin 11, mem (base+i.val)=A.words i)
    (gridWords : ∀ i : Fin 7, mem (A.grid+i.val)=B.words i)
    (ptr : vs 0=base) (column : vs 5=j.val) :
    (formula checks).natural W pub mem vs=(batch A B mem checks).words j := by
  have a0 := args (0 : Fin 11)
  change mem (base+0)=A.arguments at a0
  have a1 := args (1 : Fin 11)
  change mem (base+1)=A.streams at a1
  have a2 := args (2 : Fin 11)
  change mem (base+2)=A.maps at a2
  have a3 := args (3 : Fin 11)
  change mem (base+3)=A.incident at a3
  have a4 := args (4 : Fin 11)
  change mem (base+4)=A.grid at a4
  have a5 := args (5 : Fin 11)
  change mem (base+5)=A.dyadic at a5
  have a6 := args (6 : Fin 11)
  change mem (base+6)=A.lutBase at a6
  have a7 := args (7 : Fin 11)
  change mem (base+7)=A.lutStride at a7
  have a8 := args (8 : Fin 11)
  change mem (base+8)=A.compBase at a8
  have a9 := args (9 : Fin 11)
  change mem (base+9)=A.compStride at a9
  have a10 := args (10 : Fin 11)
  change mem (base+10)=A.countBase at a10
  have g0 := gridWords (0 : Fin 7)
  change mem (A.grid+0)=B.ports at g0
  have g1 := gridWords (1 : Fin 7)
  change mem (A.grid+1)=B.letters at g1
  have g2 := gridWords (2 : Fin 7)
  change mem (A.grid+2)=B.codeBits at g2
  have g3 := gridWords (3 : Fin 7)
  change mem (A.grid+3)=B.tileHead at g3
  have g4 := gridWords (4 : Fin 7)
  change mem (A.grid+4)=B.digit at g4
  have g5 := gridWords (5 : Fin 7)
  change mem (A.grid+5)=B.tilePage at g5
  have g6 := gridWords (6 : Fin 7)
  change mem (A.grid+6)=B.selectorPage at g6
  simp only [Nat.add_zero] at a0 g0
  cases checks <;> fin_cases j <;>
    simp [formula,batch,Header.words,HistoryBatchTape.choose,arg,grid,read,eqz,sub,add,mul,Formula.natural,
      natTest,natOp,ptr,column,a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,g0,g1,g2,g3,g4,g5,g6]

/-- Address bounds for the tables actually read while generating this party header. -/
structure ReadRoom (W : ℕ) (A : Registers) (B : Kind) (checks : Bool) (mem : ℕ → ℕ) : Prop where
  grid : A.grid+6 < 2^W
  incident : A.incident+3 < 2^W
  dyadic : A.dyadic+2 < 2^W
  lookup : A.lutBase+A.lutStride*(if checks then B.selectorPage else B.tilePage)+1 < 2^W
  counts : A.countBase+2*mem (A.dyadic+1)+1 < 2^W

set_option maxRecDepth 6000 in
set_option maxHeartbeats 800000 in
theorem formula_fits (W : ℕ) (A : Registers) (B : Kind) (checks : Bool)
    (base : ℕ) (pub : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin 13 → ℕ) (j : Fin 26)
    (args : ∀ i : Fin 11, mem (base+i.val)=A.words i)
    (gridWords : ∀ i : Fin 7, mem (A.grid+i.val)=B.words i)
    (ptr : vs 0=base) (column : vs 5=j.val) (room : base+26 < 2^W)
    (reads : ReadRoom W A B checks mem) : (formula checks).Fits W pub mem vs := by
  obtain ⟨gridRoom,incidentRoom,dyadicRoom,lookupRoom,countRoom⟩ := reads
  have one : 1 < 2^W := by omega
  have baseRoom : base < 2^W := by omega
  have baseAt (k : ℕ) (hk : k < 11) : base+k < 2^W := by omega
  have gridZero : A.grid < 2^W := by omega
  have gridAt (k : ℕ) (hk : k < 7) : A.grid+k < 2^W := by omega
  have incidentAt (k : ℕ) (hk : k ≤ 3) : A.incident+k < 2^W := by omega
  have dyadicAt (k : ℕ) (hk : k ≤ 2) : A.dyadic+k < 2^W := by omega
  have lut : A.lutBase+A.lutStride*(if checks then B.selectorPage else B.tilePage) < 2^W := by omega
  have counts : A.countBase+2*mem (A.dyadic+1) < 2^W := by omega
  have a3 : mem (base+3)=A.incident := args 3
  have a4 : mem (base+4)=A.grid := args 4
  have a5 : mem (base+5)=A.dyadic := args 5
  have a6 : mem (base+6)=A.lutBase := args 6
  have a7 : mem (base+7)=A.lutStride := args 7
  have a10 : mem (base+10)=A.countBase := args 10
  have g5 : mem (A.grid+5)=B.tilePage := gridWords 5
  have g6 : mem (A.grid+6)=B.selectorPage := gridWords 6
  unfold formula
  apply HistoryBatchTape.choose_fits (one := one)
  · trivial
  · change vs 5 < 2^W
    rw [column]
    have := j.isLt
    omega
  · cases checks <;> simp only [Bool.false_eq_true,ite_false,ite_true] at lut lookupRoom <;>
      simp (disch := omega) [arg,grid,read,add,mul,Formula.Fits,
        Formula.natural,natOp,opFits,ptr,a3,a4,a5,a6,a7,a10,g5,g6,baseAt,baseRoom,
        gridAt,gridZero,incidentAt,dyadicAt,lut,lookupRoom,counts,countRoom]

theorem program_word (W : ℕ) (A : Registers) (B : Kind) (checks : Bool)
    (base : ℕ) (pub : Fin 1→ℕ) (mem : ℕ → ℕ) (vs : Fin 13 → ℕ) (j : Fin 26)
    (args : ∀ i : Fin 11, mem (base+i.val)=A.words i)
    (gridWords : ∀ i : Fin 7, mem (A.grid+i.val)=B.words i)
    (ptr : vs 0=base) (column : vs 5=j.val)
    (fit : (formula checks).Fits W (fun _ => pub 0) mem vs) :
    (program W checks).eval (fun i => (pub i : Word W)) (fun i => (mem i : Word W))
      (fun i => (vs i : Word W))=((batch A B mem checks).words j : Word W) := by
  change ((formula checks).compile _).eval _ _ _=_
  rw [Formula.eval_compile]
  refine (Formula.value_eq_natural (formula checks) (fun _ => pub 0) mem vs fit).trans ?_
  rw [formula_word W A B checks base _ mem vs j args gridWords ptr column]


end ThreeFlat.RAM.HistoryPartyHeader

end OAI
