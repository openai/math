import OAI.Optimization.LinearProgramming.Geometry.LabelBuffers
import OAI.Optimization.LinearProgramming.Geometry.UniformGramInput
import OAI.Optimization.LinearProgramming.RAM.UniformFootprint

/-! Compute disjoint locations for ordinary, unpadded `[D,E,price]` input from `[r,s,n,i]`. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelInput

open RAM Compression

set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

def rawSize (r s n : ℕ) : ℕ := r*n+s*n+n

/-- Reserve the original input followed by an arena. Duplicate E into the prefix before D;
the prices remain at the end of the complete retained snapshot. -/
def standardBuffers (r s n : ℕ) : Buffers r s n :=
  let dual := 256+rawSize r s n
  let primal := dual+s*n
  let price := primal+r*n+s*n
  ⟨dual,primal,price,price+n,256,by omega,le_rfl,by omega,le_rfl,by decide⟩

private def addresses : List GramAllocOp :=
  [.copy 202 0, .copy 203 1, .copy 204 2, .copy 205 3, .set 14 0,
   .set 218 256, .set 221 1, .set 222 0, .reserve 219 222 202 204, .reserve 220 222 203 204,
   .reserve 223 219 221 220, .reserve 224 223 221 204, .reserve 200 218 221 224, .copy 201 218,
   .reserve 206 200 221 220, .reserve 225 206 221 219, .reserve 207 225 221 220, .reserve 208 207 221 204]

def rawAddresses : Block := gramAllocCode addresses

private theorem allowed : ∀ op∈addresses, op.allowed := by simp [addresses,GramAllocOp.allowed,CellScratchOK]

structure Positions {K : Type} (r s n index : ℕ) (m : Memory K) : Prop where
  dual : m.index 200=(standardBuffers r s n).dual
  indices : m.index 201=256
  rank : m.index 202=r
  dualRank : m.index 203=s
  columns : m.index 204=n
  designated : m.index 205=index
  primal : m.index 206=(standardBuffers r s n).primal
  prices : m.index 207=(standardBuffers r s n).price
  free : m.index 208=(standardBuffers r s n).free
  dualLength : m.index 220=s*n
  total : m.index 224=rawSize r s n
  dualSource : m.index 225=(standardBuffers r s n).primal+r*n

theorem Positions.of_frame {K : Type} {r s n i : ℕ} {m t : Memory K} (h : Positions r s n i m)
    (frame : ∀ a, 200 ≤ a → t.index a=m.index a) : Positions r s n i t := by
  constructor <;> rw [frame _ (by decide)]
  all_goals first | exact h.dual | exact h.indices | exact h.rank | exact h.dualRank | exact h.columns |
    exact h.designated | exact h.primal | exact h.prices | exact h.free | exact h.dualLength | exact h.total | exact h.dualSource

theorem rawAddresses_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (hm : m.AllData P) (r s n i : ℕ)
    (hr : m.index 0=r) (hs : m.index 1=s) (hn : m.index 2=n) (hi : m.index 3=i) :
    ∃ t c, c ≤ 4000*(r+s+n+1)^2 ∧ Block.Eval (Memory.AllData P) rawAddresses m c t ∧
      Positions r s n i t ∧ t.data=m.data ∧ ∀ a, 256 ≤ a → t.index a=m.index a := by
  obtain ⟨t,et,td,ti⟩ := gramAllocCode_eval P m m.index addresses allowed hm (fun _ _ _ => rfl)
  refine ⟨t,_,?_,et,?_,td,?_⟩
  · simp [addresses,gramAllocCost,GramAllocOp.cost,GramAllocOp.indexAfter,hr,hs,hn]
    ring_nf
    omega
  · constructor <;> rw [ti _ (by decide) (by decide)] <;>
      simp [addresses,gramAllocIndex,GramAllocOp.indexAfter,rawSize,standardBuffers,hr,hs,hn,hi]
  · intro a ha
    let permitted := ([8,9,14,200,201,202,203,204,205,206,207,208,218,219,220,221,222,223,224,225] : List ℕ).contains
    apply et.address_frame_of_list permitted (by rfl) (by rfl) a
    simp [permitted]; omega

end LabelInput
end Geometry
end LinearProgramming
end Optimization
end OAI
