import OAI.Optimization.LinearProgramming.Recovery.ConstraintBases
import OAI.Optimization.LinearProgramming.Geometry.UniformGramTimeBound
import OAI.Optimization.LinearProgramming.Geometry.UniformGramInput
import OAI.Optimization.LinearProgramming.Geometry.GramEncoding
import OAI.Optimization.LinearProgramming.Geometry.ResidualPass

/-! One fixed normal-entry routine returns a dense generating matrix of the kernel of
an independent row system. The residual reuses the cofactor workspace after Gram has
finished, so it preserves the input basis without introducing an unbounded allocation. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace ResidualROM

open RAM Matrix
open _root_.OAI.Optimization.LinearProgramming.Geometry
open scoped Matrix

private def settings : List (ℕ × ℕ) := [(31,51),(33,51),(35,58),(40,57),(41,51)]

def block : Block := .seq uniformGramInputBlock (.seq uniformGramBlock (.seq (indexMoves settings) residualPass))
def program : Program := block.compile 0 ++ [.halt 0]
def time (r n : ℕ) := 200*(r+n+1)^2+uniformGramTime r n+5+residualPassTime n+1

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The output register 58 identifies the row-major residual matrix's first entry.
The common predicate controls all scalar cells across Gram, bridging, and residual phases. -/
theorem block_spec {r n : ℕ} (E : Matrix (Fin r) (Fin n) K) (P : K→Prop)
    (hinput : ∀ j : ℕ,P ((encodedGramInput E)[j]?.getD 0)) (hE : LinearIndependent K E.row)
    (values : UniformGramValues P E) (hdelta : ∀ i j,P ((1-rowGramProjector E) i j)) :
    let l := packedGramLayout r n
    ∃ t c, c+1 ≤ time r n ∧ Block.Eval (Memory.AllData P) block (start [r,n] (encodedGramInput E)).memory c t ∧
      uniformRect n n l.sub t=kernelRows E ∧ t.index 58=l.sub ∧ t.index 51=n := by
  let l:=packedGramLayout r n
  obtain ⟨a,i,hi,ei,ah,af⟩ := uniformGramInputBlock_spec P r n (encodedGramInput E) hinput
  change uniformRect r n l.d a=gramInputMatrix r n (encodedGramInput E) at af
  have hA : uniformRect r n l.d a=E := by simpa using af
  obtain ⟨b,j,hj,ej,bp,_,bi⟩ := uniformGramBlock_spec l P a ah ei.safe_end (hA ▸ hE) (hA ▸ values)
  rw [hA] at bp
  have b51 := (bi 51 (Or.inr (by decide))).trans ah.cols
  have b57 : b.index 57 = l.out := (bi 57 (Or.inr (by decide))).trans ah.out
  have b58 : b.index 58 = l.sub := (bi 58 (Or.inr (by decide))).trans ah.sub
  let v:=movedIndices b settings
  have ev : Block.Eval (Memory.AllData P) (indexMoves settings) b 5 v := indexMoves_eval P b ej.safe_end _
  have fields : v.index 31=n ∧ v.index 33=n ∧ v.index 35=l.sub ∧ v.index 40=l.out ∧ v.index 41=n ∧ v.index 58=l.sub ∧ v.index 51=n := by
    simp [v,settings,movedIndices,b51,b57,b58]
  obtain ⟨f31,f33,f35,f40,f41,f58,f51⟩:=fields
  have vP : uniformRect n n l.out v=rowGramProjector E := by
    apply Eq.trans ?_ bp
    ext i j
    change (movedIndices b settings).data (l.out+i.val*n+j.val) = b.data (l.out+i.val*n+j.val)
    exact congrFun (movedIndices_data b settings) _
  have min:=l.minimum;have x1:=l.d_tr;have x2:=l.tr_g;have x3:=l.g_inv;have x4:=l.inv_left;have x5:=l.left_out
  obtain ⟨t,k,hk,ek,table,_,ti⟩ := residualPass_spec P (rowGramProjector E) v l.out l.sub (by omega) l.out_sub
    ev.safe_end values.zero values.one hdelta f31 f33 f35 f40 f41 vP
  exact ⟨t,_,by unfold time;omega,ei.seq (ej.seq (ev.seq ek)),table.trans (kernelRows_eq E).symm,
    (ti 58 (residualKeeps_high _ (by decide))).trans f58,(ti 51 (residualKeeps_high _ (by decide))).trans f51⟩

/-- A complete scalar RAM execution, including its fixed halt instruction. -/
theorem program_spec {r n : ℕ} (E : Matrix (Fin r) (Fin n) K) (P : K→Prop)
    (hinput : ∀ j : ℕ,P ((encodedGramInput E)[j]?.getD 0)) (hE : LinearIndependent K E.row)
    (values : UniformGramValues P E) (hdelta : ∀ i j,P ((1-rowGramProjector E) i j)) :
    ∃ c ≤ time r n, ∃ tr : Fin (c+1)→State K, Trace program (start [r,n] (encodedGramInput E)) c tr ∧
      (tr (Fin.last c)).output=some 0 ∧
      rowSpace (uniformRect n n ((tr (Fin.last c)).index 58) (tr (Fin.last c)).memory)=LinearMap.ker E.mulVecLin ∧
      ∀ i j,P ((tr i).data j) := by
  obtain ⟨t,c,hc,ev,rows,addr,_⟩:=block_spec E P hinput hE values hdelta
  obtain ⟨tr,trace,halt,mem,safe⟩:=ev.halted_trace (tag:=0)
  have hrow := (congrArg rowSpace rows).trans (kernelRows_span E hE)
  have base : (tr (Fin.last (c+1))).index 58=t.index 58 := by
    simpa only [State.memory] using congrArg (fun m : Memory K => m.index 58) mem
  refine ⟨c+1,hc,tr,trace,halt,?_,safe⟩
  rw [base,mem,addr]
  exact hrow

end ResidualROM
end Recovery
end LinearProgramming
end Optimization
end OAI
