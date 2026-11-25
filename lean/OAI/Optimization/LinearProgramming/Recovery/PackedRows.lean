import OAI.Optimization.LinearProgramming.Recovery.RowGather
import OAI.Optimization.LinearProgramming.Recovery.RowIndex
import OAI.Optimization.LinearProgramming.Elimination.UniformRowBasis

/-! The independent-row mask produced by the uniform row-rank RAM is compacted and
gathered into a true row-major basis matrix. The physical count can be used as the
row dimension in the next native Gram or geometric call. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace RowPack

open Matrix Submodule RAM BitRAM.IndexScript Elimination Compression
open _root_.OAI.Optimization.LinearProgramming.Geometry
open scoped Matrix

private def firstOps : List Instr := [.addrCopy 160 50,.addrCopy 161 55,.addrConst 162 512]
private def gatherOps : List (ℕ × ℕ) := [(31,165),(33,51),(35,57),(161,51),(169,52)]

def packFlags : Block := .seq (.straight firstOps) (.seq RowIndex.program (.seq (indexMoves gatherOps) RowGather.program))

def program : Block := .seq uniformRowBasisBlock packFlags

def packTime (r n : ℕ) := 3+(10*r+6)+(5+uniformTableTime r n (RowGather.cellTime r n))

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- There is no rank parameter in the program. The result count in register 165 comes
from scanning the actual mask, and the first packed row starts at the Gram output base. -/
theorem packFlags_spec {r n : ℕ} (l : GramLayout r n) (s : Memory K) (A : Matrix (Fin r) (Fin n) K)
    (S : Finset (Fin r)) (P : K→Prop) (h0 : P 0) (ss : s.AllData P) (H : GramHeader l s)
    (input : uniformRect r n l.d s=A) (flags : ∀ i : Fin r,s.data (l.inv+i.val)=if i∈S then 1 else 0)
    (indep : LinearIndepOn K A.row (S : Set (Fin r))) (span : Submodule.span K (A.row '' (S : Set (Fin r)))=rowSpace A) :
    ∃ t c k, c ≤ packTime r n ∧ Block.Eval (Memory.AllData P) packFlags s c t ∧ t.index 165=k ∧ k ≤ r ∧
      PacksRows A (uniformRect k n l.out t) ∧ t.index 57=l.out := by
  let a : Memory K := ⟨s.data,BitRAM.IndexScript.run firstOps s.index⟩
  have e₁ : Block.Eval (Memory.AllData P) (.straight firstOps) s 3 a := correct firstOps
    (by intro op hop; simp [firstOps] at hop; rcases hop with h|h|h <;> subst op <;> rfl) s ss
  have a160 : a.index 160=r := by simp [a,firstOps,BitRAM.IndexScript.run,update,H.rows]
  have a161 : a.index 161=l.inv := by simp [a,firstOps,BitRAM.IndexScript.run,update,H.inv]
  have a162 : a.index 162=512 := by simp [a,firstOps,BitRAM.IndexScript.run,update]
  have ai (p : ℕ) (h : p < 160) : a.index p=s.index p := by
    simp [a,firstOps,BitRAM.IndexScript.run,update,show p≠160 by omega,show p≠161 by omega,show p≠162 by omega]
  have hlo := l.minimum; have hdt := l.d_tr; have htg := l.tr_g; have hgi := l.g_inv
  have hil := l.inv_left; have hlo' := l.left_out
  obtain ⟨b,c,hc,e₂,rep,bd,bi⟩ := RowIndex.program_spec P S a e₁.safe_end h0 a160 a161 a162 (by omega) (by decide) flags
  let rows := (List.finRange r).filter (·∈S)
  have length_le : rows.length ≤ r := by simpa [rows] using List.length_filter_le (fun i : Fin r => decide (i∈S)) (List.finRange r)
  have bf (p : ℕ) (h : p < 160) : b.index p=s.index p :=
    (bi p (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))).trans (ai p h)
  have b162 : b.index 162=512 := (bi 162 (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))).trans a162
  let v := movedIndices b gatherOps
  have e₃ : Block.Eval (Memory.AllData P) (indexMoves gatherOps) b 5 v := indexMoves_eval P b e₂.safe_end _
  have fields : v.index 14=0 ∧ v.index 31=rows.length ∧ v.index 33=n ∧ v.index 35=l.out ∧
      v.index 161=n ∧ v.index 162=512 ∧ v.index 169=l.d ∧ v.index 165=rows.length ∧ v.index 57=l.out := by
    simp [v,gatherOps,movedIndices,bf 14 (by decide),bf 51 (by decide),bf 57 (by decide),bf 52 (by decide),
      H.zero,H.cols,H.out,H.d,rep.count,b162,rows]
  obtain ⟨v14,v31,v33,v35,v161,v162,v169,v165,v57⟩ := fields
  have idx (i : Fin rows.length) : v.index (512+i.val)=(rows.get i).val := by
    rw [show v.index (512+i.val)=b.index (512+i.val) from movedIndices_other b gatherOps _ (by simp [gatherOps]; omega)]
    exact rep.entries _ _ (by simp [rows])
  have Ainput : uniformRect r n l.d v=A := by
    ext i j
    have val := congrFun (congrFun input i) j
    change v.data (l.d+i.val*n+j.val)=_
    rw [show v.data = b.data from movedIndices_data _ _]
    exact (bd _ (by omega) (by omega)).trans val
  obtain ⟨t,j,hj,e₄,table,_,ti⟩ := RowGather.program_spec rows.get A v P e₃.safe_end length_le v14 v31 v33 v35
    v161 v162 v169 Ainput idx (by decide) (by omega) (by omega)
  have time : uniformTableTime rows.length n (RowGather.cellTime r n) ≤ uniformTableTime r n (RowGather.cellTime r n) := by
    unfold uniformTableTime uniformEntryTime; gcongr
  refine ⟨t,_,rows.length,?_,e₁.seq (e₂.seq (e₃.seq e₄)),(ti 165 (Or.inr (by decide))).trans v165,length_le,?_,
    (ti 57 (Or.inr (by decide))).trans v57⟩
  · unfold packTime; omega
  · rw [table]
    exact RowGather.packedRows_span A S indep span

/-- Composition with the actual rank scan from its ordinary two-dimension input tape. -/
theorem public_spec (r n : ℕ) (xs : List K) (P : K→Prop) (input : ∀ j : ℕ,P (xs[j]?.getD 0))
    (h0 : P 0) (h1 : P 1) (hn : ∀ x,P x→P (-x))
    («partial» : ∀ i j : Fin r,∀ u : Finset (Fin n), P (∑ z∈u,rectangularTape r n xs i z*rectangularTape r n xs j z))
    (register : let A := rectangularTape r n xs
      ∀ S : Finset (Fin r), let T := maskGram (A*Aᵀ) (flag S)
      ∀ k < r,∀ reg : BirdRegister r,P (reg.read T (birdLayer T k))) :
    let A := rectangularTape r n xs
    let l := packedGramLayout r n
    ∃ t c k, c ≤ rowBasisTime r n+packTime r n ∧ Block.Eval (Memory.AllData P) program (start [r,n] xs).memory c t ∧
      t.index 165=k ∧ k ≤ r ∧ PacksRows A (uniformRect k n l.out t) ∧ t.index 57=l.out := by
  let A := rectangularTape r n xs
  let S := visitedBasis (A*Aᵀ) r
  obtain ⟨v,a,ha,e,hstate,hg,hd⟩ := uniformRowBasisBlock_safe r n xs P input h0 h1 hn «partial» register
  obtain ⟨hI,hS,_⟩ := visitedBasis_spec Aᵀ
  have li : LinearIndepOn K A.row (S : Set (Fin r)) := by simpa [S] using hI
  have sp : Submodule.span K (A.row '' (S : Set (Fin r)))=rowSpace A := by simpa [S,rowSpace] using hS
  obtain ⟨t,b,k,hb,ee,count,hk,packs,addr⟩ := packFlags_spec _ v A S P h0 e.safe_end hg hd hstate.flags li sp
  exact ⟨t,a+b,k,by omega,e.seq ee,count,hk,packs,addr⟩

end RowPack
end Recovery
end LinearProgramming
end Optimization
end OAI
