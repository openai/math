import OAI.Optimization.LinearProgramming.Geometry.UniformGramLayout
import OAI.Optimization.LinearProgramming.Geometry.UniformTable
import OAI.Optimization.LinearProgramming.Compression.UniformBirdInput

/-! Prepare the Gram projector's disjoint arrays from ordinary runtime dimensions
and an unmodified scalar input tape. Allocation touches only the address bank. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Compression

inductive GramAllocOp
  | copy (dst src : ℕ)
  | set (dst value : ℕ)
  | reserve (dst base rows cols : ℕ)
  deriving DecidableEq

namespace GramAllocOp

def code : GramAllocOp → Block
  | .copy dst src => .op (.addrCopy dst src)
  | .set dst n => .op (.addrConst dst n)
  | .reserve dst base rows cols => cellAddress dst 8 9 base cols rows 14

def indexAfter (h : ℕ → ℕ) : GramAllocOp → ℕ → ℕ
  | .copy d s => Function.update h d (h s)
  | .set d n => Function.update h d n
  | .reserve d base rows cols => Function.update h d (h base+h rows*h cols+h 14)

def cost (h : ℕ → ℕ) : GramAllocOp → ℕ
  | .copy _ _ | .set _ _ => 1
  | .reserve _ _ rows cols => h rows*(4*h cols+5)+4*h 14+5

def allowed : GramAllocOp → Prop
  | .copy _ s => s≠8 ∧ s≠9
  | .set _ _ => True
  | .reserve d b r c => CellScratchOK d 8 9 c r 14 ∧ b≠8 ∧ b≠9 ∧ r≠8 ∧ r≠9 ∧ c≠8 ∧ c≠9

end GramAllocOp

def gramAllocCode : List GramAllocOp → Block
  | [] => .skip
  | op::ops => .seq op.code (gramAllocCode ops)

def gramAllocIndex (h : ℕ → ℕ) : List GramAllocOp → ℕ → ℕ
  | [] => h
  | op::ops => gramAllocIndex (op.indexAfter h) ops

def gramAllocCost (h : ℕ → ℕ) : List GramAllocOp → ℕ
  | [] => 0
  | op::ops => op.cost h + gramAllocCost (op.indexAfter h) ops

private theorem gramAllocOp_eval {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (h : ℕ→ℕ) (a : GramAllocOp) (ha : a.allowed)
    (hs : m.AllData P) (hi : ∀ j, j≠8 → j≠9 → m.index j=h j) :
    ∃ t, Block.Eval (Memory.AllData P) a.code m (a.cost h) t ∧ t.data=m.data ∧
      ∀ j, j≠8 → j≠9 → t.index j=a.indexAfter h j := by
  cases a with
  | copy dst src =>
    let t := m.putIndex dst (m.index src)
    refine ⟨t, Block.Eval.op_addrCopy _ _ _ hs hs,rfl,?_⟩
    intro j j8 j9
    by_cases hj : j=dst
    · subst j; simpa [t,GramAllocOp.indexAfter] using hi src ha.1 ha.2
    · simpa [t,GramAllocOp.indexAfter,hj] using hi j j8 j9
  | set dst n =>
    refine ⟨m.putIndex dst n,Block.Eval.op_addrConst _ _ _ hs hs,rfl,?_⟩
    intro j j8 j9
    by_cases hj : j=dst
    · subst j; simp [GramAllocOp.indexAfter]
    · simpa [GramAllocOp.indexAfter,hj] using hi j j8 j9
  | reserve dst b r c =>
    obtain ⟨hh,b8,b9,r8,r9,c8,c9⟩ := ha
    obtain ⟨t,e,hd,hf,hv⟩ := cellAddress_spec (fun v => ∀ p, P (v p)) m hs dst 8 9 b c r 14 hh
    have eb := hi b b8 b9
    have er := hi r r8 r9
    have ec := hi c c8 c9
    have ez := hi 14 (by decide) (by decide)
    rw [er,ec,ez] at e
    refine ⟨t,e,hd,?_⟩
    intro j j8 j9
    by_cases hj : j=dst
    · subst j; simpa [GramAllocOp.indexAfter,eb,er,ec,ez] using hv
    · simpa [GramAllocOp.indexAfter,hj] using (hf j hj j8 j9).trans (hi j j8 j9)

private theorem gramAlloc_eval {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (h : ℕ→ℕ) (ops : List GramAllocOp)
    (ha : ∀ a∈ops, a.allowed) (hs : m.AllData P) (hi : ∀ j, j≠8 → j≠9 → m.index j=h j) :
    ∃ t, Block.Eval (Memory.AllData P) (gramAllocCode ops) m (gramAllocCost h ops) t ∧
      t.data=m.data ∧ ∀ j, j≠8 → j≠9 → t.index j=gramAllocIndex h ops j := by
  induction ops generalizing m h with
  | nil => exact ⟨m,.skip hs,rfl,hi⟩
  | cons a rest ih =>
    obtain ⟨u,e,ud,ui⟩ := gramAllocOp_eval P m h a (ha _ List.mem_cons_self) hs hi
    obtain ⟨t,et,td,ti⟩ := ih u (a.indexAfter h) (fun q hq => ha q (List.mem_cons_of_mem _ hq)) e.safe_end ui
    exact ⟨t,e.seq et,td.trans ud,ti⟩

/-- Run the represented address program without changing scalar memory. -/
alias gramAllocCode_eval := gramAlloc_eval

/-- Fixed address arithmetic. The final two moves satisfy the forward
copy subroutine's source/destination cursor convention. -/
def gramAllocSteps : List GramAllocOp :=
  [.copy 50 0, .copy 51 1, .set 14 0, .set 15 64,
   .reserve 52 15 50 51, .reserve 53 52 50 51, .reserve 54 53 51 50,
   .reserve 55 54 50 50, .reserve 56 55 50 50, .reserve 57 56 51 50,
   .reserve 58 57 51 51, .reserve 59 58 50 50, .reserve 60 59 50 50,
   .copy 1 52, .copy 11 53]

def uniformGramInputBlock : Block := .seq (gramAllocCode gramAllocSteps) birdCopyInput

private theorem gramAllocSteps_allowed : ∀ a∈gramAllocSteps, a.allowed := by
  simp [gramAllocSteps,GramAllocOp.allowed,CellScratchOK]

private def gramInputTime (r n : ℕ) : ℕ :=
  gramAllocCost (fun j => ([r,n] : List ℕ)[j]?.getD 0) gramAllocSteps + (6*(r*n)+3)

private theorem gramInputTime_le (r n : ℕ) : gramInputTime r n ≤ 200*(r+n+1)^2 := by
  simp [gramInputTime,gramAllocSteps,gramAllocCost, GramAllocOp.cost,GramAllocOp.indexAfter]
  nlinarith [Nat.zero_le (r^2),Nat.zero_le (n^2),Nat.zero_le (r*n)]

/-- Bootstrap one fixed Gram projector from the dimensions and coefficient tape.
The original data are copied forward using scalar register 0 only after entry 0 is consumed. -/
theorem uniformGramInputBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (r n : ℕ) (input : List K) (hs : ∀ j : ℕ, P (input[j]?.getD 0)) :
    let s := (start [r,n] input).memory
    let l := packedGramLayout r n
    ∃ t k, k ≤ 200*(r+n+1)^2 ∧ Block.Eval (Memory.AllData P) uniformGramInputBlock s k t ∧
      GramHeader l t ∧ uniformRect r n l.d t = (fun i j => input[i.val*n+j.val]?.getD 0) := by
  let s := (start [r,n] input).memory
  let l := packedGramLayout r n
  obtain ⟨u,e,ud,hf⟩ := gramAlloc_eval P s s.index gramAllocSteps gramAllocSteps_allowed hs
    (fun _ _ _ => rfl)
  have fields : GramHeader l u := by
    constructor <;> rw [hf _ (by decide) (by decide)] <;>
      simp [l,packedGramLayout,gramAllocIndex,gramAllocSteps,GramAllocOp.indexAfter,s,start,State.memory]
  have hb : u.index 1=l.d := by
    rw [hf _ (by decide) (by decide)]
    simp [l,packedGramLayout,gramAllocIndex,gramAllocSteps,GramAllocOp.indexAfter,s,start,State.memory]
  have he : u.index 11=l.d + r*n := by
    rw [hf _ (by decide) (by decide)]
    simp [l,packedGramLayout,gramAllocIndex,gramAllocSteps,GramAllocOp.indexAfter,s,start,State.memory]
  obtain ⟨t,et,copied,keep⟩ := birdCopyInput_spec P u l.d (r*n) hb he
    (by dsimp [l,packedGramLayout]; omega) e.safe_end
  refine ⟨t,_,gramInputTime_le r n,e.seq et,fields.of_frame (fun q hq =>
    keep q (by omega) (by omega)),?_⟩
  ext i j
  have h := copied (i.val*n+j.val) (rectOffset_lt i j)
  change t.data (l.d + i.val*n + j.val) = s.data (i.val*n + j.val)
  simpa only [Nat.add_assoc, ud] using h

end Geometry
end LinearProgramming
end Optimization
end OAI
