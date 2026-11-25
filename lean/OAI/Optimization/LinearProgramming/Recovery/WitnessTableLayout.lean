import OAI.Optimization.LinearProgramming.Recovery.PairBuilderHeaders
import OAI.Optimization.LinearProgramming.Geometry.UniformTable

/-! Input and output tapes of the solver for a masked system with its marked
first coordinate fixed to one. The stored tableau has the right-hand side first. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessTable

open RAM RAM.Call RAM.Tape Geometry Polynomial

/-- The first unused scalar cell after the masked opposite matrix and flags. -/
def tableBase (h n : ℕ) : ℕ := 256+(h*n+n)+h*n+n*n+n

def words (h n : ℕ) : ℕ := (n+1)*(h+n+1)
def capacity (h n : ℕ) : ℕ := words h n+2
def destination (h n : ℕ) : ℕ := tableBase h n+words h n+1

/-- Populate the table walker and the caller's solver descriptor from 200–203. -/
def headers : HeaderPlan 220 :=
  let one : AddressTerm 220 := .val 1
  let two : AddressTerm 220 := .val 2
  let rows : AddressTerm 220 := .reg 31
  let cols : AddressTerm 220 := .reg 33
  let source : AddressTerm 220 := .reg 202
  let out : AddressTerm 220 := .reg 203
  let length : AddressTerm 220 := .reg 56
  [(15,one),(16,two),(31,(.reg 201)+one),(33,(.reg 200)+one),(35,out),
   (40,source-rows),(41,.reg 201),(55,out),(56,rows*cols),(57,.val 208),
   (58,two),(60,length+two),(208,rows),(209,cols),(210,out+length+one),(211,.reg 201)]

structure Ready (k n source out : ℕ) (ix : Fin 220 → ℕ) : Prop where
  one : ix 15 = 1
  two : ix 16 = 2
  rows : ix 31 = n+1
  cols : ix 33 = k+1
  output : ix 35 = out
  offset : ix 40 = source-(n+1)
  stride : ix 41 = n
  scalarBase : ix 55 = out
  scalarLength : ix 56 = (n+1)*(k+1)
  addressBase : ix 57 = 208
  addressLength : ix 58 = 2
  bound : ix 60 = (n+1)*(k+1)+2
  firstDim : ix 208 = n+1
  secondDim : ix 209 = k+1
  next : ix 210 = out+(n+1)*(k+1)+1
  originalWidth : ix 211 = n

private theorem computed (ix : Fin 220 → ℕ) :
    Ready (ix 200) (ix 201) (ix 202) (ix 203) (headers.output ix) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private def used (ix : Fin 220 → ℕ) (i : Fin 220) : ℕ :=
  if i = 200 then ix 200 else if i = 201 then ix 201
  else if i = 202 then ix 202 else if i = 203 then ix 203 else 0

/-- Only the four declared source registers contribute to this actual setup cost. -/
private theorem setup_cost (ix : Fin 220 → ℕ) : headers.cost ix = headers.cost (used ix) := by
  apply PairBuilder.plan_cost_congr
  intro i hi
  have sources : PairBuilder.needed headers = ({200,201,202,203} : Finset (Fin 220)) := by decide
  rw [sources] at hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with h|h|h|h <;> subst i <;> rfl

noncomputable def clockPolynomial : Polynomial ℕ :=
  headers.budget.comp (300*(X+1)^2) + 120*(X+1)^4

theorem source_bound (h n : ℕ) :
    256+(h*n+n) ≤ 300*(h+n+1)^2 ∧ tableBase h n ≤ 300*(h+n+1)^2 := by
  unfold tableBase
  constructor <;> ring_nf <;> omega

/-- Numeric bound for the row/column scanner and its transposed-cell lookup. -/
theorem table_clock (k n : ℕ) (hn : n ≤ k) :
    uniformTableTime (n+1) (k+1) (k*(4*n+5)+4*n+15) ≤ 120*(k+1)^4 := by
  calc
    _ ≤ uniformTableTime (k+1) (k+1) (k*(4*k+5)+4*k+15) := by
      unfold uniformTableTime uniformEntryTime
      gcongr
    _ ≤ _ := by unfold uniformTableTime uniformEntryTime; ring_nf; omega

/-- No restriction on unrelated incoming address registers is needed. -/
theorem header_run {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (hm : m.AllData P) (k n source out : ℕ)
    (hk : m.index 200=k) (hn : m.index 201=n)
    (hs : m.index 202=source) (ho : m.index 203=out)
    (fit : n ≤ k) (sourceFits : source ≤ 300*(k+1)^2) (outFits : out ≤ 300*(k+1)^2) :
    ∃ t j, j ≤ headers.budget.eval (300*(k+1)^2) ∧
      Block.Eval (Memory.AllData P) (headers.code 220) m j t ∧ t.data = m.data ∧
      Ready k n source out (fun i => t.index i) := by
  let ix : Fin 220 → ℕ := fun i => m.index i
  have kFit : k ≤ 300*(k+1)^2 := by ring_nf; omega
  have fits (i : Fin 220) : used ix i ≤ 300*(k+1)^2 := by
    unfold used
    split
    · exact hk.trans_le kFit
    split
    · exact hn.trans_le (fit.trans kFit)
    split
    · exact hs.trans_le sourceFits
    split
    · exact ho.trans_le outFits
    · exact Nat.zero_le _
  obtain ⟨t,j,run,cost,data,idx⟩ := HeaderPlan.correct headers 220 le_rfl m ix (fun _ => rfl) hm
  have budget : j ≤ headers.budget.eval (300*(k+1)^2) := by
    rw [setup_cost] at cost
    exact cost.trans (headers.cost_le (used ix) _ fits)
  have ready := computed ix
  change Ready (m.index 200) (m.index 201) (m.index 202) (m.index 203) _ at ready
  rw [hk,hn,hs,ho] at ready
  exact ⟨t,j,budget,run,data,(funext idx : (fun i : Fin 220 => t.index i) = _).symm ▸ ready⟩

end WitnessTable
end Recovery
end LinearProgramming
end Optimization
end OAI
