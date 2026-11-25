import OAI.Hierarchy.DescentTerminalIssuedBook
import OAI.Hierarchy.DescentTerminalScanFacts
import OAI.Hierarchy.DescentTerminalBookRowCount
import OAI.Hierarchy.DescentTerminalUniversalWrite

namespace OAI
/-! # Computing the number of paid rows from the same short primitive word lists -/
namespace Hierarchy.DescentTerminalLocalPortBook
open Computability.VPVNP.BurstRAM PrivateRAM DescentTerminalRecipeRows DescentTerminalBinPack ProtocolRAM
open ThreeFlat.Routing CallPool ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {G V M A a q w : ℕ}
theorem actual_rows (s : Site) (f : Room s G V M A) (names : s.Name→Word a) (args : s.Arg→Word a) :
    (issue s f names args).rows q=s.rows q := by
  have g:=size_live s f names args
  have v:=arity_live s f names args
  change (∑g,poolBatchCount _ q) + bins q _ +1 = (∑g,poolBatchCount _ q) + bins q _ +1
  rw [show (issue s f names args).arity=s.arity from funext v]
  exact congrArg (fun n=>n + bins q s.arity + 1) (Finset.sum_congr rfl (fun i _=>congrArg (poolBatchCount · q) (g i)))

def countRow (head table : Bank) : Expr := .lookup table (.lookup head .row)
theorem published {S : ℕ} (sites : Fin S→Site) (f : ∀i,Room (sites i) G V M A) (labels : ∀i,(sites i).Name→Word a)
    (refs : ∀i,(sites i).Arg→Word a) (head table : Bank) (dst : ℕ) (m : Memory w)
    (issued : ∀i:Fin S,head.read m (i.val:Word w)=((issue (sites i) (f i) (labels i) (refs i)).bytes.val:Word w))
    (rom : ∀i:Fin (Book.Bytes G V M A a),table.read m (i.val:Word w)=countTable q i) (i : Fin S) :
    ProtocolRAM.image dst S (countRow head table) m (dst+i.val)=((sites i).rows q:Word w) := by
  rw [DescentTerminalChipRuntime.image_at]
  simp [countRow,Expr.eval,issued,rom,countTable,Book.bytes_read,actual_rows]
theorem scan_cost (head table : Bank) (dst S : ℕ) (m : Memory w) (low : head.Fits w dst) (tl : table.Fits w dst)
    (fit : dst+S<2^w) : (scan w dst S (countRow head table)).Exec m
    (ProtocolRAM.image dst S (countRow head table) m) (4+28*S) ∧ CheapCode (scan w dst S (countRow head table)) := by
  refine ⟨?_,scan_cheap w dst S (countRow head table)⟩
  rw [show 4+28*S = 4+S*(2*(countRow head table).work+4) by
    change 4+28*S=4+S*28
    omega]
  exact @scan_exec w dst S (countRow head table) m ⟨tl,low,trivial⟩ fit
end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
