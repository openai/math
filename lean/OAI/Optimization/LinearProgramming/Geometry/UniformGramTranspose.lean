import OAI.Optimization.LinearProgramming.Geometry.UniformGramProducts
import OAI.Optimization.LinearProgramming.Geometry.UniformCopyTable

/-! Fixed transpose preparation for the uniform Gram product phases. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM
open scoped Matrix

def gramTransposeSettings : List (ℕ × ℕ) := [(31,51),(33,50),(35,53),(40,52),(41,51)]

def gramTransposePhase : Block :=
  .seq (indexMoves gramTransposeSettings) (uniformTableBlock (GramCopy.cell true))

def gramTransposeTime (r n : ℕ) := 5 + uniformTableTime n r ((r+n)*(4*(r+n)+5)+4*(r+n)+6)

theorem gramTransposePhase_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r n : ℕ} (l : GramLayout r n) (P : K → Prop) (s : Memory K) (hh : GramHeader l s)
    (hs : s.AllData P) :
    ∃ t k, k ≤ gramTransposeTime r n ∧ Block.Eval (Memory.AllData P) gramTransposePhase s k t ∧
      uniformRect n r l.tr t = (uniformRect r n l.d s)ᵀ ∧ GramPhaseFrame l l.tr (n*r) s t := by
  let u := movedIndices s gramTransposeSettings
  have e : Block.Eval (Memory.AllData P) (indexMoves gramTransposeSettings) s 5 u :=
    indexMoves_eval P s hs _
  have fields : u.index 31=n ∧ u.index 33=r ∧ u.index 35=l.tr ∧ u.index 40=l.d ∧ u.index 41=n := by
    simp [u,gramTransposeSettings,movedIndices,hh.rows,hh.cols,hh.d,hh.tr]
  obtain ⟨f31,f33,f35,f40,f41⟩ := fields
  let keep (q : ℕ) := q=14 ∨ q=40 ∨ q=41 ∨ 50≤q
  have hmin := l.minimum
  have hdtr := l.d_tr
  have sources (i : Fin n) (j : Fin r) :
      let a := GramCopy.tableSource true (u.index 40) (u.index 41) i j
      7≤a ∧ (a<l.tr ∨ l.tr+n*r≤a) := by
    have ho := rectOffset_lt j i
    change 7 ≤ u.index 40 + j.val * u.index 41 + i.val ∧
      (u.index 40 + j.val * u.index 41 + i.val < l.tr ∨
        l.tr+n*r ≤ u.index 40 + j.val * u.index 41 + i.val)
    rw [f40,f41]
    omega
  have hc := GramCopy.cell_callback true P (fun a => 7≤a) keep u n r l.tr (r+n)
    (by omega) (by omega) (f41.trans_le (by omega)) (by decide)
    (fun q hq => by dsimp [keep] at hq; omega) (by decide) (by decide) sources
  obtain ⟨t,k,hk,et,val,fd,fi⟩ := uniformTableBlock_spec (GramCopy.cell true) P (fun a => 7≤a)
    keep u n r l.tr _ _ hc (fun q hq => by dsimp [keep] at hq; unfold TableScratch; omega)
    (fun i j => by omega) f31 f33 f35 e.safe_end
  refine ⟨t,_,Nat.add_le_add_left hk 5,e.seq et,?_,?_,?_⟩
  · ext i j
    have h := congrFun (congrFun val i) j
    simpa [GramCopy.tableSource,f40,f41,u,uniformRect] using h
  · intro q hq hdis _
    exact (fd q (by omega) hdis).trans (congrFun (movedIndices_data s _) q)
  · intro q hq
    apply Eq.trans (fi q (Or.inr (show keep q by dsimp [keep]; omega)))
    apply movedIndices_other
    simp [gramTransposeSettings]
    omega

end Geometry
end LinearProgramming
end Optimization
end OAI
