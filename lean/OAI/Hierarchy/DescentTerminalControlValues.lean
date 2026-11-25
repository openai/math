import OAI.Hierarchy.DescentTerminalBookRows
import OAI.Hierarchy.DescentTerminalBookPublish
import OAI.Hierarchy.DescentNativeBankLookup

namespace OAI
/-! # Primitive-port row and vertex counts from the six physical local book fields -/
namespace Hierarchy.DescentTerminalLocalPortBook
open DescentTerminalRecipeRows DescentTerminalBinPack ProtocolRAM
open ThreeFlat.Routing CallPool
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {G V M A a q S w : ℕ}

def Book.portRows (bk : Book G V M A a) (q : ℕ) : ℕ := ∑g,poolBatchCount (bk.size g) q

theorem actual_ports (s : Site) (f : Room s G V M A) (names : s.Name→Word a) (args : s.Arg→Word a) :
    (issue s f names args).portRows q=s.portRows q := by
  apply Finset.sum_congr rfl
  intro g _
  exact congrArg (poolBatchCount · q) (size_live s f names args g)

def portTable (q : ℕ) (j : ℕ) : ℕ :=
  if h : j < Book.Bytes G V M A a then (Book.fromBytes (⟨j,h⟩ : Fin (Book.Bytes G V M A a))).portRows q else 0

theorem portTable_at (bk : Book G V M A a) :
    portTable (G:=G) (V:=V) (M:=M) (A:=A) (a:=a) q bk.bytes.val=bk.portRows q := by
  unfold portTable
  split
  · exact congrArg (fun u : Book G V M A a => u.portRows q) (Book.bytes_read bk)
  · rename_i outside
    exact (outside bk.bytes.isLt).elim

def portExpr (parts : Book.Parts) (table : Bank) : Expr := .lookup table (Book.expression parts)

theorem port_value (parts : Book.Parts) (table : Bank) (m : Memory w)
    (sites : Fin S→Site) (fit : ∀i,Room (sites i) G V M A)
    (names : ∀i,(sites i).Name→Word a) (args : ∀i,(sites i).Arg→Word a)
    (issued : Book.Issued parts (fun i=>issue (sites i) (fit i) (names i) (args i)) m)
    (room : Book.Bytes G V M A a ≤ table.size) (wide : table.size<2^w)
    (stored : ∀i : Fin (Book.Bytes G V M A a),m (table.base+i.val)=
      (portTable (G:=G) (V:=V) (M:=M) (A:=A) (a:=a) q i.val:Word w))
    (i : Fin S) : (portExpr parts table).eval m (i.val:Word w)=((sites i).portRows q:Word w) := by
  let bk:=issue (sites i) (fit i) (names i) (args i)
  have read:=Book.numeric parts _ m issued i
  rw [portExpr,DescentIssuedTerminalId.lookup_nat table m _ _ bk.bytes.val read
    (bk.bytes.isLt.trans_le room) wide,stored bk.bytes,portTable_at]
  exact congrArg (fun n : ℕ=>(n:Word w)) (actual_ports (sites i) (fit i) (names i) (args i))

theorem nodes_value (parts : Book.Parts) (m : Memory w) (sites : Fin S→Site) (fit : ∀i,Room (sites i) G V M A)
    (names : ∀i,(sites i).Name→Word a) (args : ∀i,(sites i).Arg→Word a)
    (issued : Book.Issued parts (fun i=>issue (sites i) (fit i) (names i) (args i)) m) (i : Fin S) :
    (parts 1).source.read m (i.val:Word w)=((sites i).nodes:Word w) := by
  exact issued.source i 1

end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
