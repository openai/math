import OAI.Hierarchy.DescentTerminalRoleWords
import OAI.Hierarchy.DescentTerminalSumExpr

namespace OAI
/-! Six input banks, six shift arrays and the two terminal role table payloads. -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentTerminalVertexFields DescentEpochTagKeys DescentSIMDLookup DescentBundleHistory ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {U:Type} {n A G p R N M wb slots:ℕ} (old:Codec U n)
local notation "sz" => width n A G p R
local notation "data" => Sources n A G p R N M
local notation "srcType" => Sources n A G p R N M
local notation "mux" => ∏j:Fin 6,2^(sz j*N*M)
structure Shelf where
  input : Fin 6→Bank
  shift : Fin 6→Bank
  menu : Bank

def scale (f:Fin 6) := ∏j:Fin f.val,2^(sz (j.castLE f.isLt.le)*N*M)
def term (s:Shelf) (f:Fin 6) : Expr := .lookup (s.shift f) (.lookup (s.input f) .row)
def emit (s:Shelf) : Expr := .lookup s.menu (sumExpr (term s) (List.finRange 6))
def scaleWords (f:Fin 6) : Vector (Word wb) (2^(sz f*N*M)) :=
  Vector.ofFn fun j=>((scale (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) f*j.val:ℕ):Word wb)
def menuWords : Vector (Word wb) mux := Vector.ofFn fun j=>((rolePanel old (finPiFinEquiv.symm j : data)).val:Word wb)

structure Static (s:Shelf) (m:Memory wb) : Prop where
  radix : ∀f,(s.shift f).bits=sz f*N*M
  shift : ∀f,∀j:Fin (2^(sz f*N*M)),m ((s.shift f).base+j.val)=(scaleWords (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) f)[j]
  slots : mux≤ s.menu.size
  key : mux≤2^wb
  dictionary : ∀j:Fin mux,m (s.menu.base+j.val)=(menuWords (N:=N) (M:=M) (A:=A) (G:=G) (p:=p) (R:=R) old)[j]

def tally (xs:List (List SliceCode)) := (xs.map (fun row=>(row.map SliceCode.count).sum)).sum
def localCount (slots:ℕ) (src:Arrays n A G p R) : Word (Nat.clog 2 (slots+1)) :=
  if (fields src).primitive=0 then 0 else (tally (metadata (fields src)) : Word (Nat.clog 2 (slots+1)))
def countPanel (slots:ℕ) (x:srcType) : Word (Nat.clog 2 (slots+1)*N*M) :=
  encode (Nat.clog 2 (slots+1)*N) M (fun g=>encode (Nat.clog 2 (slots+1)) N (fun u=>localCount slots (node x g u)))

def countWords (slots:ℕ) : Vector (Word wb) mux :=
  Vector.ofFn fun j=>((countPanel slots (finPiFinEquiv.symm j:srcType)).val:Word wb)

/-- This shelf can reuse both the six physical source banks and all six shift ROMs of the
role emitter. Only the numeric output table differs. -/
structure CountStatic (slots:ℕ) (s:Shelf) (m:Memory wb) : Prop where
  radix : ∀f,(s.shift f).bits=sz f*N*M
  shift : ∀f,∀j:Fin (2^(sz f*N*M)),m ((s.shift f).base+j.val)=(scaleWords (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) f)[j]
  capacity : mux≤ s.menu.size
  key : mux≤2^wb
  table : ∀j:Fin mux,m (s.menu.base+j.val)=(countWords (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) slots)[j]

/-- Two tables on the same six source digits and the six shared shift arrays still
fit in the original half-word advice budget. -/
theorem combined_advice (h:ℕ) (space:(∑f:Fin 6,sz f*N*M)+3≤h/2) :
    (∑f:Fin 6,2^(sz f*N*M))+mux+mux≤2^(h/2) := by
  have each (f:Fin 6) : 2^(sz f*N*M)≤ mux := by
    rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_le_pow_right (by decide) (Finset.single_le_sum (f:=fun i : Fin 6=>sz i*N*M) (fun _ _=>Nat.zero_le _) (Finset.mem_univ f))
  have cost : (∑f:Fin 6,2^(sz f*N*M))≤6*mux := by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun f _=>each f)
  calc
    _≤8*mux:=by omega
    _=2^((∑f:Fin 6,sz f*N*M)+3):=by rw [Finset.prod_pow_eq_pow_sum,pow_add];ring
    _≤_:=Nat.pow_le_pow_right (by decide) space

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
