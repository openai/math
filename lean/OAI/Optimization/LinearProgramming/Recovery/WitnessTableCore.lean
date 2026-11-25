import OAI.Optimization.LinearProgramming.Recovery.WitnessTableCells
import OAI.Optimization.LinearProgramming.Recovery.WitnessTableLayout

/-! Fixed, ordinary RAM code constructing the full augmented solver input after
support deletion. It reads the rectangular matrix already present on the tape. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessTable

open RAM RAM.Call Geometry Polynomial

def block : Block := .seq (headers.code 220) (uniformTableBlock cell)

/-- Final registers of the two logical solver input tapes and its output reservation. -/
structure OutputHeader {K : Type} (h n : ℕ) (m : Memory K) : Prop where
  scalarBase : m.index 55 = tableBase h n
  scalarLength : m.index 56 = words h n
  addressBase : m.index 57 = 208
  addressLength : m.index 58 = 2
  bound : m.index 60 = capacity h n
  firstDim : m.index 208 = n+1
  secondDim : m.index 209 = h+n+1
  next : m.index 210 = destination h n
  originalWidth : m.index 211 = n

/-- All scalar arithmetic in this writer consists of copying the original
matrix entries and writing zero and one. The clock counts the actual address
computations, both table loops and the descriptor initialization. -/
theorem execute {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {h n : ℕ}
    (C : Matrix (Fin (h+n)) (Fin n) K) (hn : 0 < n)
    (P : K → Prop) (m : Memory K) (hm : m.AllData P) (h0 : P 0) (h1 : P 1)
    (height : m.index 200 = h+n) (width : m.index 201 = n)
    (source : m.index 202 = 256+(h*n+n)) (out : m.index 203 = tableBase h n)
    (input : uniformRect (h+n) n (256+(h*n+n)) m = C) :
    ∃ t steps, steps ≤ clockPolynomial.eval (h+n) ∧
      Block.Eval (Memory.AllData P) block m steps t ∧
      uniformRect (n+1) (h+n+1) (tableBase h n) t = matrix C hn ∧ OutputHeader h n t := by
  have fits := source_bound h n
  obtain ⟨u,s,hs,init,values,reg⟩ := header_run P m hm (h+n) n (256+(h*n+n)) (tableBase h n)
    height width source out (by omega) fits.1 fits.2
  have sourceTable : uniformRect (h+n) n (256+(h*n+n)) u = C := by
    unfold uniformRect at input ⊢
    rw [values,input]
  have sep : 256+(h*n+n)+(h+n)*n ≤ tableBase h n := by
    unfold tableBase
    rw [Nat.add_mul]
    omega
  obtain ⟨t,k,hk,table,filled,_,_,keep⟩ :=
    table_spec C hn P u init.safe_end h0 h1 reg.one reg.two reg.rows reg.cols reg.output reg.offset
      reg.stride (by omega) (by omega) sep sourceTable
  refine ⟨t,s+k,?_,init.seq table,filled,?_⟩
  · have tableCost := hk.trans (table_clock (h+n) n (by omega))
    simpa [clockPolynomial,Polynomial.eval_comp] using Nat.add_le_add hs tableCost
  · exact ⟨(keep 55 (by decide)).trans reg.scalarBase,(keep 56 (by decide)).trans reg.scalarLength,
      (keep 57 (by decide)).trans reg.addressBase,(keep 58 (by decide)).trans reg.addressLength,
      (keep 60 (by decide)).trans reg.bound,(keep 208 (by decide)).trans reg.firstDim,
      (keep 209 (by decide)).trans reg.secondDim,(keep 210 (by decide)).trans reg.next,
      (keep 211 (by decide)).trans reg.originalWidth⟩

end WitnessTable
end Recovery
end LinearProgramming
end Optimization
end OAI
