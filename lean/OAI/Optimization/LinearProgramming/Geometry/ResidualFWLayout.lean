import OAI.Optimization.LinearProgramming.Geometry.UniformGramLayout
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeRAMGradient
import OAI.Optimization.LinearProgramming.RAM.RAMIndex
import OAI.Optimization.LinearProgramming.RAM.UniformFootprint

/-! Route the completed Gram projector to a fresh residual table and initialize the
permanent addresses of the Frank–Wolfe label test. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace ResidualFWLayout

open RAM RAM.Tape
variable {r n : ℕ}

/-- New scalar buffers start just beyond both determinant work squares. -/
def layout (l : GramLayout r n) : FWRAM.Layout n where
  matrix := l.workB + r*r
  point := l.workB + r*r + n*n
  gradient := l.workB + r*r + n*n + n
  reserved := by
    have := l.minimum
    have := l.d_tr
    have := l.tr_g
    have := l.g_inv
    have := l.inv_left
    have := l.left_out
    have := l.out_sub
    have := l.sub_workA
    have := l.workA_workB
    omega
  afterMatrix := le_rfl
  afterPoint := le_rfl

/-- Source and residual tables are disjoint, even if the earlier buffers have padding. -/
theorem source_end (l : GramLayout r n) : l.out+n*n ≤ (layout l).matrix := by
  have := l.out_sub
  have := l.sub_workA
  have := l.workA_workB
  change l.out+n*n ≤ l.workB+r*r
  omega

theorem source_reserved (l : GramLayout r n) : 8 ≤ l.out := by
  have := l.minimum
  have := l.d_tr
  have := l.tr_g
  have := l.g_inv
  have := l.inv_left
  have := l.left_out
  omega

/-- Stable information required after the completed residual pass. -/
structure Buffers {K : Type*} (l : GramLayout r n) (i : Fin n) (m : Memory K) : Prop where
  dimension : m.index 51 = n
  target : m.index 62 = i.val
  matrix : m.index 63 = (layout l).matrix
  point : m.index 64 = (layout l).point
  gradient : m.index 65 = (layout l).gradient

theorem Buffers.of_high_frame {K : Type*} {l : GramLayout r n} {i : Fin n} {m t : Memory K}
    (h : Buffers l i m) (f : ∀ j, 42 < j → t.index j = m.index j) : Buffers l i t :=
  ⟨(f 51 (by decide)).trans h.dimension,(f 62 (by decide)).trans h.target,
   (f 63 (by decide)).trans h.matrix,(f 64 (by decide)).trans h.point,
   (f 65 (by decide)).trans h.gradient⟩

/-- Input pointers and extents consumed by the residual table emitter. -/
structure TableInputs {K : Type*} (l : GramLayout r n) (m : Memory K) : Prop where
  rows : m.index 31 = n
  cols : m.index 33 = n
  output : m.index 35 = (layout l).matrix
  source : m.index 40 = l.out
  stride : m.index 41 = n

private def squareEnd (base dim : Fin 66) : AddressTerm 66 :=
  .binary .plus (.reg base) (.binary .times (.reg dim) (.reg dim))

private def gradientEnd : AddressTerm 66 := .binary .plus (.reg 64) (.reg 51)

private def assign (e : AddressTerm 66) (dst : ℕ) : Block :=
  .seq (e.code 66) (.op (.addrCopy dst 66))

private def residualMoves : List (ℕ × ℕ) := [(31,51),(33,51),(35,63),(40,57),(41,51)]

/-- Set 63–65 to Q, point and gradient. The added quantities are relative
extents, so the running time is independent of the numerical base addresses. -/
def prepareResidual : Block :=
  .seq (assign (squareEnd 60 50) 63) <| .seq (assign (squareEnd 63 51) 64) <|
    .seq (assign gradientEnd 65) (indexMoves residualMoves)

private def fwMoves : List (ℕ × ℕ) := [(23,51),(25,64),(28,65),(29,62),(34,63)]

/-- Prepare the actual address registers consumed by the Frank–Wolfe label block. -/
def prepareFW : Block := indexMoves fwMoves

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem assign_spec (P : K → Prop) (e : AddressTerm 66) (dst : ℕ)
    (m : Memory K) (hm : m.AllData P) :
    let env := fun j : Fin 66 => m.index j
    ∃ t k, k ≤ e.cost env+1 ∧ Block.Eval (Memory.AllData P) (assign e dst) m k t ∧
      t.data = m.data ∧ (∀ j < 66, j ≠ dst → t.index j = m.index j) ∧
      t.index dst = e.value env := by
  let env := fun j : Fin 66 => m.index j
  obtain ⟨k,z,ev,hk,hd,hf,hv⟩ := e.correct env 66 m le_rfl (fun _ => rfl) hm
  let t := z.putIndex dst (z.index 66)
  have cp : Block.Eval (Memory.AllData P) (.op (.addrCopy dst 66)) z 1 t :=
    eval_copyI z ev.safe_end dst 66
  exact ⟨t,k+1,Nat.add_le_add_right hk 1,ev.seq cp,hd,
    fun j hj hn => (getPutDifferent _ hn).trans (hf _ hj),(getPutSame ..).trans hv⟩

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem square_cost (m : Memory K) (base dim : Fin 66) (N : ℕ) (h : m.index dim=N) :
    (squareEnd base dim).cost (fun j => m.index j)+1 = 10+5*N+8*N^2 := by
  simp only [squareEnd,AddressTerm.cost,AddressTerm.value,AddressOp.cost,AddressOp.value,Nat.mul_eq,h]
  ring

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem gradient_cost (m : Memory K) (h : m.index 51=n) :
    gradientEnd.cost (fun j => m.index j)+1 = 5+4*n := by
  change m.index (51 : Fin 66).val = n at h
  simp only [gradientEnd,AddressTerm.cost,AddressTerm.value,AddressOp.cost,h]
  ring

/-- Every address outside the output pointers and private work range survives. -/
theorem prepareResidual_index_frame {safe : Memory K → Prop} {s t : Memory K} {k : ℕ}
    (run : Block.Eval safe prepareResidual s k t) (j : ℕ)
    (h : j ∉ ([31,33,35,40,41,63,64,65,66,67,68,69,70,71] : List ℕ)) :
    t.index j = s.index j := by
  let permitted := ([31,33,35,40,41,63,64,65,66,67,68,69,70,71] : List ℕ).contains
  apply run.address_frame_of_list permitted (by rfl) (by rfl) j
  simpa [permitted] using h

/-- Execute the routing with the verified Gram header and the reserved target.
The scalar bank and Gram header are intact at the end. -/
theorem prepareResidual_spec (P : K → Prop) (l : GramLayout r n) (i : Fin n) (entry : Memory K)
    (hg : GramHeader l entry) (hi : entry.index 62=i.val) (hmem : entry.AllData P) :
    ∃ t k, k ≤ 64*(r+n+1)^2 ∧ Block.Eval (Memory.AllData P) prepareResidual entry k t ∧
      t.data = entry.data ∧ GramHeader l t ∧ Buffers l i t ∧ TableInputs l t := by
  obtain ⟨s₁,a,ha,e₁,hd₁,hf₁,hq⟩ := assign_spec P (squareEnd 60 50) 63 entry hmem
  change s₁.index 63 = entry.index 60+entry.index 50*entry.index 50 at hq
  rw [hg.b,hg.rows] at hq
  have hn₁ : s₁.index 51 = n := (hf₁ 51 (by decide) (by decide)).trans hg.cols
  obtain ⟨s₂,b,hb,e₂,hd₂,hf₂,hp⟩ := assign_spec P (squareEnd 63 51) 64 s₁ e₁.safe_end
  change s₂.index 64 = s₁.index 63+s₁.index 51*s₁.index 51 at hp
  rw [hq,hn₁] at hp
  have hn₂ : s₂.index 51 = n := (hf₂ 51 (by decide) (by decide)).trans hn₁
  obtain ⟨s₃,c,hc,e₃,hd₃,hf₃,hg'⟩ := assign_spec P gradientEnd 65 s₂ e₂.safe_end
  change s₃.index 65 = s₂.index 64+s₂.index 51 at hg'
  rw [hp,hn₂] at hg'
  let t := movedIndices s₃ residualMoves
  have em := indexMoves_eval P s₃ e₃.safe_end residualMoves
  have eval : Block.Eval (Memory.AllData P) prepareResidual entry (a+(b+(c+5))) t :=
    .seq e₁ (.seq e₂ (.seq e₃ em))
  refine ⟨t,_,?_,eval,(movedIndices_data _ _).trans (hd₃.trans (hd₂.trans hd₁)),?_,?_,?_⟩
  · rw [square_cost entry 60 50 r hg.rows] at ha
    rw [square_cost s₁ 63 51 n hn₁] at hb
    rw [gradient_cost s₂ hn₂] at hc
    ring_nf
    omega
  · apply hg.of_frame
    intro j hj
    apply prepareResidual_index_frame eval
    simp only [List.mem_cons,List.mem_nil_iff,or_false]
    omega
  · have hn₃ := (hf₃ 51 (by decide) (by decide)).trans hn₂
    have h62 := (hf₃ 62 (by decide) (by decide)).trans
      ((hf₂ 62 (by decide) (by decide)).trans ((hf₁ 62 (by decide) (by decide)).trans hi))
    have h63 := (hf₃ 63 (by decide) (by decide)).trans ((hf₂ 63 (by decide) (by decide)).trans hq)
    have h64 := (hf₃ 64 (by decide) (by decide)).trans hp
    constructor <;> simp [t,residualMoves,movedIndices,hn₃,h62,h63,h64,hg',layout]
  · have hn₃ := (hf₃ 51 (by decide) (by decide)).trans hn₂
    have h63 := (hf₃ 63 (by decide) (by decide)).trans ((hf₂ 63 (by decide) (by decide)).trans hq)
    have h57 := (hf₃ 57 (by decide) (by decide)).trans
      ((hf₂ 57 (by decide) (by decide)).trans ((hf₁ 57 (by decide) (by decide)).trans hg.out))
    constructor <;> simp [t,residualMoves,movedIndices,hn₃,h63,h57,layout]

/-- Prepare all five permanent Frank–Wolfe registers from the retained
header. This is five actual copies and preserves the complete residual table. -/
theorem prepareFW_spec (P : K → Prop) (l : GramLayout r n) (i : Fin n) (s : Memory K)
    (hb : Buffers l i s) (hs : s.AllData P) :
    ∃ t, Block.Eval (Memory.AllData P) prepareFW s 5 t ∧ t.data=s.data ∧
      FWRAM.Addresses (layout l) i t ∧ Buffers l i t ∧
      ∀ j, j ∉ ([23,25,28,29,34] : List ℕ) → t.index j=s.index j := by
  refine ⟨movedIndices s fwMoves,indexMoves_eval P s hs _,movedIndices_data _ _,?_,?_,?_⟩
  · constructor <;> simp [fwMoves,movedIndices,hb.dimension,hb.point,hb.gradient,hb.target,hb.matrix]
  · constructor <;> simp [fwMoves,movedIndices,hb.dimension,hb.point,hb.gradient,hb.target,hb.matrix]
  · intro j hj
    apply movedIndices_other
    simp only [fwMoves,List.mem_cons,List.mem_nil_iff,or_false] at *
    intro z hz
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> simp_all

end ResidualFWLayout
end Geometry
end LinearProgramming
end Optimization
end OAI
