import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.DescentSixPartySeed

namespace OAI
/-! # Literal field instructions and addresses for the six-party geometry -/

namespace Hierarchy.DescentOrdinaryDestRAM
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Fin.CommRing
variable {w : ℕ}
def times (c : ℕ) (x : Expr) : Expr := match c with
  | 0=>.lit 0
  | k+1=>.op .add x (times k x)
theorem times_eval (c : ℕ) (x : Expr) (m : Memory w) (a : Word w) :
    (times c x).eval m a=(c:Word w)*x.eval m a := by
  induction c with
  | zero=>simp [times,Expr.eval]
  | succ c ih=>
    simp only [times,Expr.eval,RowOp.opcode,BinaryOp.eval,ih,Nat.cast_succ]
    ring

end Hierarchy.DescentOrdinaryDestRAM

namespace Hierarchy.DescentOrdinaryRawRows
open DescentOrdinaryDestRAM DescentSixParty ProtocolRAM
open scoped Classical
noncomputable section
inductive Column where | src | dst | width | core | repeats deriving DecidableEq
inductive Born where | arm (s : Fin 2) | supply (s : Fin 8) deriving DecidableEq

def Born.index : Born→Fin 10
  | .arm s=>⟨s.val,by have :=s.isLt;omega⟩
  | .supply s=>⟨2+s.val,by have :=s.isLt;omega⟩

structure Sources where
  pair : Bank
  birthOwner : Bank
  oldOwner : Bank
  oldSrc : Bank
  resolvedTarget : Bank
  oldWidth : Bank
  oldMark : Bank
  widthROM : Fin 8→Bank
  multiplicityROM : Fin 8→Bank

private def sum (x y : Expr) := Expr.op .add x y
def readRecord (bank : Bank) (stride off : ℕ) (i : Expr) := Expr.lookup bank (sum (times stride i) (.lit off))
def Sources.bornRead (S : Sources) (j : Fin 6) := readRecord S.birthOwner 6 j.val .row
def Sources.pairRead (S : Sources) (off : ℕ) := readRecord S.pair 9 off .row

/-- The eight finite tariffs are the actual fixed z-fold profile widths. -/
def Sources.born (S : Sources) (b : ℕ) (name : Born) : Column→Expr
  | .src=>match name with | .arm s=>S.bornRead (demandDst s) | .supply s=>S.bornRead (supplySrc s)
  | .dst=>match name with
    | .arm s=>.lookup S.oldOwner (S.pairRead (4+2*s.val))
    | .supply s=>S.bornRead (supplyDst s)
  | .width=>match name with
    | .arm s=>.lookup S.oldWidth (S.pairRead (1+s.val))
    | .supply s=>.lookup (S.widthROM s) (S.pairRead 8)
  | .core=>.lit 1
  | .repeats=>match name with
    | .arm _=>.lit b
    | .supply s=>.lookup (S.multiplicityROM s) (S.pairRead 8)

def Sources.old (S : Sources) (b : ℕ) : Column→Expr
  | .src=>.lookup S.oldOwner (.lookup S.oldSrc .row)
  | .dst=>.lookup S.resolvedTarget .row
  | .width=>.lookup S.oldWidth .row
  | .core=>.lookup S.oldMark .row
  | .repeats=>.branch .eq (.lookup S.oldMark .row) (.lit 0) (.lit 1) (.lit b)

export Sources (bornRead pairRead born old)

def band (j : ℕ) : Born :=
  if h : j%10<2 then .arm ⟨j%10,h⟩ else .supply ⟨j%10-2,by have:=Nat.mod_lt j (by decide : 0<10);omega⟩

theorem band_at (s : Born) : band s.index.val=s := by
  cases s with
  | arm i=>fin_cases i <;> decide
  | supply i=>fin_cases i <;> decide

structure Output where
  base : ℕ
  dest : ℕ
  vals : ℕ

variable {w n e : ℕ} (S : Sources) (O : Output) (b : ℕ) (f : Column)
def Output.address (O : Output) (e j : ℕ) := Expr.op .add (.lit (O.base+e+j)) (times 10 .row)
def Output.addr (O : Output) (e j i : ℕ) := O.base+e+10*i+j

export Output (address addr)

end
end Hierarchy.DescentOrdinaryRawRows

end OAI
