import OAI.Optimization.LinearProgramming.Geometry.LabelBuffers
import OAI.Optimization.LinearProgramming.Geometry.UniformGramInput
import OAI.Optimization.LinearProgramming.RAM.UniformFootprint

/-! A fixed address-only program constructs all geometry registers from a relocatable caller ABI. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelInput

open RAM Matrix Compression BorderBatch

set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

private def alloc : List GramAllocOp :=
  [.copy 129 202, .copy 130 204, .copy 131 206, .copy 132 207, .copy 133 208,
   .copy 136 201, .copy 146 205, .copy 147 200, .copy 148 203,
   .set 14 0, .set 209 0, .set 210 1, .set 211 3, .set 212 6, .set 213 100,
   .reserve 214 210 202 210, .reserve 215 210 204 210, .reserve 216 209 215 215,
   .reserve 217 209 216 215, .reserve 138 209 217 213,
   .reserve 134 208 211 204, .reserve 143 134 202 204, .reserve 144 143 204 210,
   .reserve 140 201 202 210, .reserve 141 140 212 204, .reserve 142 141 202 210,
   .reserve 145 142 204 214, .copy 149 144, .set 128 0, .copy 135 134, .copy 137 136, .set 139 0]

/-- The serialized instructions read dimensions and locations at run time. The degree-three
rounding precision is computed in the address bank. Reservations take time depending only
on the number of newly allocated cells, independently of the numerical base pointers. -/
def prepareHeader : Block := gramAllocCode alloc

private theorem alloc_ok : ∀ op ∈ alloc, op.allowed := by simp [alloc,GramAllocOp.allowed,CellScratchOK]

/-- Exactly the direct address registers that may change. The scalar bank is untouched. -/
def modifiedHeaderRegisters : List ℕ :=
  [8,9,14,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,
    209,210,211,212,213,214,215,216,217]

theorem prepareHeader_frame {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {S : Memory K → Prop} {m t : Memory K} {c : ℕ} (e : Block.Eval S prepareHeader m c t)
    (a : ℕ) (ha : a ∉ modifiedHeaderRegisters) : t.index a=m.index a := by
  apply e.address_frame_of_list modifiedHeaderRegisters.contains (by rfl) (by rfl) a
  simpa using ha

private theorem sourceWords (f : ℕ → ℕ) :
    gramAllocIndex f alloc 128 = 0 ∧
    gramAllocIndex f alloc 129 = f 202 ∧
    gramAllocIndex f alloc 130 = f 204 ∧
    gramAllocIndex f alloc 131 = f 206 ∧
    gramAllocIndex f alloc 132 = f 207 ∧
    gramAllocIndex f alloc 133 = f 208 := by
  repeat' apply And.intro
  all_goals rfl

private theorem pivotWords (f : ℕ → ℕ) :
    gramAllocIndex f alloc 134 = f 208+3*f 204 ∧
    gramAllocIndex f alloc 135 = f 208+3*f 204 ∧
    gramAllocIndex f alloc 136 = f 201 ∧
    gramAllocIndex f alloc 137 = f 201 ∧
    gramAllocIndex f alloc 138 = 100*(f 204+1)^3 ∧
    gramAllocIndex f alloc 139 = 0 := by
  repeat' apply And.intro
  all_goals try rfl
  all_goals simp [alloc,gramAllocIndex,GramAllocOp.indexAfter]
  all_goals ring

private theorem workspaceWords (f : ℕ → ℕ) :
    gramAllocIndex f alloc 140 = f 201+f 202 ∧
    gramAllocIndex f alloc 141 = f 201+f 202+6*f 204 ∧
    gramAllocIndex f alloc 142 = f 201+f 202+6*f 204+f 202 ∧
    gramAllocIndex f alloc 143 = f 208+3*f 204+f 202*f 204 ∧
    gramAllocIndex f alloc 144 = f 208+3*f 204+f 202*f 204+f 204 ∧
    gramAllocIndex f alloc 145 = f 201+f 202+6*f 204+f 202+f 204*(f 202+1) := by
  repeat' apply And.intro
  all_goals try rfl
  all_goals simp [alloc,gramAllocIndex,GramAllocOp.indexAfter]
  all_goals left; omega

private theorem callerWords (f : ℕ → ℕ) :
    gramAllocIndex f alloc 146 = f 205 ∧
    gramAllocIndex f alloc 147 = f 200 ∧
    gramAllocIndex f alloc 148 = f 203 ∧
    gramAllocIndex f alloc 149 = f 208+3*f 204+f 202*f 204+f 204 := by
  repeat' apply And.intro
  all_goals try rfl
  all_goals simp [alloc,gramAllocIndex,GramAllocOp.indexAfter]

private theorem allocationTime (f : ℕ → ℕ) :
    gramAllocCost f alloc ≤ 5000*(f 202+f 204+1)^3 := by
  simp [alloc,gramAllocCost,GramAllocOp.cost,GramAllocOp.indexAfter]
  ring_nf
  omega

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r s n : ℕ}

theorem prepareHeader_spec (P : K → Prop) (m : Memory K) (hm : m.AllData P)
    (x : Buffers r s n) (D : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K)
    (price : Fin n → K) (i : Fin n) (h : Inputs x D E price i m) :
    ∃ t c, c ≤ 5000*(r+n+1)^3 ∧ Block.Eval (Memory.AllData P) prepareHeader m c t ∧
      Header x D E price i t ∧ t.data=m.data ∧ ∀ a ∉ modifiedHeaderRegisters, t.index a=m.index a := by
  obtain ⟨t,et,td,ti⟩ := gramAllocCode_eval P m m.index alloc alloc_ok hm (fun _ _ _ => rfl)
  have regs (a : ℕ) (ha : a ≠ 8) (ha' : a ≠ 9) := ti a ha ha'
  let setupReady := x.layout.Ready D (Fin.elim0 : Fin 0 → Fin n) t
  obtain ⟨c128,c129,c130,c131,c132,c133⟩ := sourceWords m.index
  obtain ⟨c134,c135,c136,c137,c138,c139⟩ := pivotWords m.index
  obtain ⟨c140,c141,c142,c143,c144,c145⟩ := workspaceWords m.index
  obtain ⟨c146,c147,c148,c149⟩ := callerWords m.index
  simp only [h.rank,h.columns,h.dualRank,h.index,h.freeAddr,h.indexAddr,h.dualAddr,h.primalAddr,h.priceAddr] at c128 c129 c130 c131 c132 c133 c134 c135 c136 c137 c138 c139 c140 c141 c142 c143 c144 c145 c146 c147 c148 c149
  have regEq (a : ℕ) (v : ℕ) (h8 : a≠8) (h9 : a≠9) (hval : gramAllocIndex m.index alloc a=v) : t.index a=v :=
    (regs a h8 h9).trans hval
  replace c128 := regEq 128 _ (by decide) (by decide) c128
  replace c129 := regEq 129 _ (by decide) (by decide) c129
  replace c130 := regEq 130 _ (by decide) (by decide) c130
  replace c131 := regEq 131 _ (by decide) (by decide) c131
  replace c132 := regEq 132 _ (by decide) (by decide) c132
  replace c133 := regEq 133 _ (by decide) (by decide) c133
  replace c134 := regEq 134 _ (by decide) (by decide) c134
  replace c135 := regEq 135 _ (by decide) (by decide) c135
  replace c136 := regEq 136 _ (by decide) (by decide) c136
  replace c137 := regEq 137 _ (by decide) (by decide) c137
  replace c138 := regEq 138 _ (by decide) (by decide) c138
  replace c139 := regEq 139 _ (by decide) (by decide) c139
  replace c140 := regEq 140 _ (by decide) (by decide) c140
  replace c141 := regEq 141 _ (by decide) (by decide) c141
  replace c142 := regEq 142 _ (by decide) (by decide) c142
  replace c143 := regEq 143 _ (by decide) (by decide) c143
  replace c144 := regEq 144 _ (by decide) (by decide) c144
  replace c145 := regEq 145 _ (by decide) (by decide) c145
  replace c146 := regEq 146 _ (by decide) (by decide) c146
  replace c147 := regEq 147 _ (by decide) (by decide) c147
  replace c148 := regEq 148 _ (by decide) (by decide) c148
  replace c149 := regEq 149 _ (by decide) (by decide) c149
  have rd : setupReady := ⟨c128,c129,c130,c131,c132,c133,c134,c136,c140,c141,c142,c143,c144,c145,
    (fun q => q.elim0),fun a b => td ▸ h.primal a b⟩
  refine ⟨t,_,?_,et,⟨rd,c135,c137,c138,c139,c146,c147,c148,c149,fun a b => td ▸ h.dual a b,
    fun b => td ▸ h.prices b⟩,td,prepareHeader_frame et⟩
  simpa only [h.rank,h.columns] using allocationTime m.index

end LabelInput
end Geometry
end LinearProgramming
end Optimization
end OAI
