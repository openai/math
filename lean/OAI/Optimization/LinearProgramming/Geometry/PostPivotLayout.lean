import OAI.Optimization.LinearProgramming.Geometry.UniformGramInput
import OAI.Optimization.LinearProgramming.Geometry.ResidualFWLayout

/-! Allocate the Gram, residual and Frank–Wolfe arrays after the caller's retained
data. The already rounded primal table remains in place. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PostPivotLayout

open RAM Compression

/-- Read the rounded primal matrix at `d` and allocate every subsequent table from `free`. -/
def layout (r n d free : ℕ) (hd : 256 ≤ d) (hfree : d + r*n ≤ free) : GramLayout r n :=
  let g := free + n*r
  let inv := g + r*r
  let left := inv + r*r
  let out := left + n*r
  let sub := out + n*n
  let a := sub + r*r
  { d := d, tr := free, g := g, inv := inv, left := left, out := out, sub := sub,
    workA := a, workB := a + r*r, minimum := by omega, d_tr := hfree, tr_g := le_rfl,
    g_inv := le_rfl, inv_left := le_rfl, left_out := le_rfl, out_sub := le_rfl,
    sub_workA := le_rfl, workA_workB := le_rfl }

/-- The first free scalar address after the residual table, point and gradient. -/
theorem footprint (r n d free : ℕ) (hd : 256 ≤ d) (hfree : d+r*n ≤ free) :
    (ResidualFWLayout.layout (layout r n d free hd hfree)).gradient + n =
      free + 2*n*r + 5*r^2 + 2*n^2 + 2*n := by
  simp only [ResidualFWLayout.layout,layout]
  ring

/-- The retained primal matrix and every address below `free` precede all new tables. -/
theorem first_new_table (r n d free : ℕ) (hd : 256 ≤ d) (hfree : d+r*n ≤ free) :
    (layout r n d free hd hfree).d = d ∧ (layout r n d free hd hfree).tr = free :=
  ⟨rfl,rfl⟩

/-- Stable fields supplied by the rounded-pivot caller. -/
structure Inputs {K : Type*} {n : ℕ} (r d free : ℕ) (i : Fin n) (s : Memory K) : Prop where
  rows : s.index 129 = r
  cols : s.index 130 = n
  primal : s.index 134 = d
  designation : s.index 146 = i.val
  freeBase : s.index 149 = free

private def steps : List GramAllocOp :=
  [.copy 50 129, .copy 51 130, .copy 52 134, .copy 53 149, .copy 62 146, .set 14 0,
   .reserve 54 53 51 50, .reserve 55 54 50 50, .reserve 56 55 50 50,
   .reserve 57 56 51 50, .reserve 58 57 51 51, .reserve 59 58 50 50, .reserve 60 59 50 50]

/-- Fixed, index-only code. Reservation advances by the requested area, independent
of the initial numerical value of the base address. -/
def prepare : Block := gramAllocCode steps

private theorem allowed : ∀ a ∈ steps, a.allowed := by
  simp [steps,GramAllocOp.allowed,CellScratchOK]

/-- Caller metadata and every other address outside the header and two counter
registers survive the allocation. -/
theorem prepare_index_frame {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {safe : Memory K → Prop} {s t : Memory K} {k : ℕ}
    (e : Block.Eval safe prepare s k t) (j : ℕ)
    (h : j ∉ ([8,9,14,50,51,52,53,54,55,56,57,58,59,60,62] : List ℕ)) :
    t.index j = s.index j := by
  let permitted := ([8,9,14,50,51,52,53,54,55,56,57,58,59,60,62] : List ℕ).contains
  apply e.address_frame_of_list permitted (by rfl) (by rfl) j
  simpa [permitted] using h

/-- Populate the actual Gram and designated-coordinate address registers. -/
theorem prepare_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (r n d free : ℕ) (i : Fin n) (s : Memory K)
    (hd : 256 ≤ d) (hfree : d+r*n ≤ free) (h : Inputs r d free i s) (hm : s.AllData P) :
    ∃ t k, k ≤ 64*(r+n+1)^2 ∧ Block.Eval (Memory.AllData P) prepare s k t ∧
      t.data=s.data ∧ GramHeader (layout r n d free hd hfree) t ∧ t.index 62=i.val ∧
      ∀ j, 63 ≤ j → t.index j=s.index j := by
  obtain ⟨t,e,td,hf⟩ := gramAllocCode_eval P s s.index steps allowed hm (fun _ _ _ => rfl)
  refine ⟨t,_,?_,e,td,?_,?_,?_⟩
  · simp [steps,gramAllocCost,GramAllocOp.cost,GramAllocOp.indexAfter,h.rows,h.cols]
    nlinarith [Nat.zero_le (r^2),Nat.zero_le (n^2),Nat.zero_le (r*n)]
  · constructor <;> rw [hf _ (by decide) (by decide)] <;>
      simp [steps,gramAllocIndex,GramAllocOp.indexAfter,layout,h.rows,h.cols,h.primal,h.freeBase]
  · rw [hf _ (by decide) (by decide)]
    simp [steps,gramAllocIndex,GramAllocOp.indexAfter,h.designation]
  · intro j hj
    apply prepare_index_frame e
    simp only [List.mem_cons,List.mem_nil_iff,or_false]
    omega

end PostPivotLayout
end Geometry
end LinearProgramming
end Optimization
end OAI
