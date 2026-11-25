import OAI.Optimization.LinearProgramming.Geometry.UniformCofactor
import OAI.Optimization.LinearProgramming.Geometry.UniformGramProducts

/-! Compute the shared reciprocal once and run all inverse entries in the
uniform table code. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Compression

def firstGramDetSettings : List (ℕ × ℕ) := [(0,50),(1,54),(11,59),(12,60)]
def gramInverseSettings : List (ℕ × ℕ) :=
  [(1,58),(31,50),(33,50),(35,55),(40,54),(41,50)]

def saveGramReciprocal : Block := .seq (.op (.const 7 1)) (.op (.div 15 7 6))

def uniformGramInversePhase : Block :=
  .seq (indexMoves firstGramDetSettings) (.seq (uniformDetBlock uniformBirdCell)
    (.seq saveGramReciprocal (.seq (indexMoves gramInverseSettings) uniformInverseTable)))

def gramInverseTime (r : ℕ) := 12 + 2000*(r+1)^7 + uniformTableTime r r (uniformCofactorTime r)

/-- The matrix used in a determinant request for an inverse. -/
def requestedGramMatrix {K : Type*} [Field K] {r : ℕ} (G : Matrix (Fin r) (Fin r) K) :
    Option (Fin r × Fin r) → Matrix (Fin r) (Fin r) K
  | none => G
  | some (i,j) => G.updateRow j (Pi.single i 1)

theorem uniformGramInversePhase_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r n : ℕ} (l : GramLayout r n) (P : K → Prop) (s : Memory K) (hh : GramHeader l s)
    (hs : s.AllData P) (hp0 : P 0) (hp1 : P 1) (hpneg : ∀ x, P x → P (-x))
    (hdet : (uniformRect r r l.g s).det ≠ 0) (hrec : P (uniformRect r r l.g s).det⁻¹)
    (hbird : ∀ a k, k<r → ∀ z : BirdRegister r,
      let A := requestedGramMatrix (uniformRect r r l.g s) a
      P (z.read A (birdLayer A k)))
    (hscaled : ∀ i j : Fin r, let G := uniformRect r r l.g s
      P (G.det⁻¹ * (G.updateRow j (Pi.single i 1)).det)) :
    ∃ t cost, cost ≤ gramInverseTime r ∧ Block.Eval (Memory.AllData P) uniformGramInversePhase s cost t ∧
      uniformRect r r l.inv t=(uniformRect r r l.g s)⁻¹ ∧ GramPhaseFrame l l.inv (r*r) s t := by
  let G := uniformRect r r l.g s
  let u := movedIndices s firstGramDetSettings
  have eMove : Block.Eval (Memory.AllData P) (indexMoves firstGramDetSettings) s 4 u := indexMoves_eval P s hs _
  have fu : u.index 0=r ∧ u.index 1=l.g ∧ u.index 11=l.workA ∧ u.index 12=l.workB := by
    simp [u,firstGramDetSettings,movedIndices,hh.rows,hh.g,hh.a,hh.b]
  obtain ⟨u0,u1,u11,u12⟩ := fu
  have uFrame (q : ℕ) (hq : q=14 ∨ 50≤q) : u.index q=s.index q := by
    apply movedIndices_other
    simp [firstGramDetSettings]; omega
  have u14 := (uFrame 14 (by decide)).trans hh.zero
  have hmin := l.minimum; have dt := l.d_tr; have tg := l.tr_g; have gi := l.g_inv
  have il := l.inv_left; have lo := l.left_out; have os := l.out_sub
  have sa := l.sub_workA; have ab := l.workA_workB
  have uG : uniformMatrix r (u.index 1) u = G := by
    rw [u1]
    ext i j; exact congrFun (movedIndices_data s firstGramDetSettings) _
  obtain ⟨v,k,hk,eDet,v6,vd⟩ := uniformDetBlock_spec uniformBirdCell uniformBirdCell_spec P u r u0
    (by rw [u1]; omega) (by rw [u1,u11]; omega) (by rw [u11,u12]; exact ab)
    u14 eMove.safe_end hp0 hp1 hpneg (by rw [uG]; exact hbird none)
  rw [uG] at v6
  have vi (q : ℕ) (hq : q ∉ ({2,3,4,5,6,7,8,9,10,13} : Finset ℕ)) := uniformDet_address_frame eDet q hq
  have vFrame (q : ℕ) (hq : q=14 ∨ 50≤q) : v.index q=s.index q :=
    (vi q (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)).trans (uFrame q hq)
  let h := v.putData 7 1
  let w := h.putData 15 G.det⁻¹
  have hp1' : P ((1 : ℚ) : K) := by simpa using hp1
  have eh : Block.Eval (Memory.AllData P) (.op (.const 7 1)) v 1 h := by
    simpa [h] using Block.Eval.op_const (safe := Memory.AllData P) v 7 (1 : ℚ) eDet.safe_end
      (Memory.AllData.putData (P := P) eDet.safe_end 7 hp1')
  have hv6 : h.data 6 = G.det := by simpa [h] using v6
  have divEq : h.data 7 / h.data 6 = G.det⁻¹ := by simp [h,v6]
  have ew : Block.Eval (Memory.AllData P) (.op (.div 15 7 6)) h 1 w := by
    have ez : h.data 6 ≠ 0 := hv6 ▸ hdet
    simpa only [w,← divEq] using Block.Eval.op_div (safe := Memory.AllData P) h 15 7 6 ez
      eh.safe_end (eh.safe_end.putData _ (divEq ▸ hrec))
  have er : Block.Eval (Memory.AllData P) saveGramReciprocal v 2 w := eh.seq ew
  let z := movedIndices w gramInverseSettings
  have es : Block.Eval (Memory.AllData P) (indexMoves gramInverseSettings) w 6 z := indexMoves_eval P w er.safe_end _
  have wh : GramHeader l w := hh.of_frame fun q hq => vFrame q (hq.imp_right And.left)
  have iz : z.index 1=l.sub ∧ z.index 31=r ∧ z.index 33=r ∧ z.index 35=l.inv ∧
      z.index 40=l.g ∧ z.index 41=r := by
    simp [z,gramInverseSettings,movedIndices,wh.rows,wh.g,wh.inv,wh.sub]
  obtain ⟨z1,z31,z33,z35,z40,z41⟩ := iz
  have zi (q : ℕ) (hq : q=0 ∨ q=11 ∨ q=12 ∨ q=14 ∨ 50≤q) : z.index q=v.index q := by
    apply movedIndices_other
    simp [gramInverseSettings]; omega
  have z0 := (zi 0 (by decide)).trans ((vi 0 (by decide)).trans u0)
  have za := (zi 11 (by decide)).trans ((vi 11 (by decide)).trans u11)
  have zb := (zi 12 (by decide)).trans ((vi 12 (by decide)).trans u12)
  have z14 := (zi 14 (by decide)).trans ((vi 14 (by decide)).trans u14)
  have z58 := (zi 58 (by decide)).trans ((vFrame 58 (by decide)).trans hh.sub)
  have zd (q : ℕ) (hq : 64≤q) (hdis : q<l.sub ∨ l.workB+r*r≤q) : z.data q=s.data q := by
    have hv := vd q (by omega) (by rw [u11]; omega) (by rw [u12]; omega)
    have e : z.data q=v.data q := by simp [z,w,h,show q ≠ 15 by omega,show q ≠ 7 by omega]
    exact e.trans (hv.trans (congrFun (movedIndices_data s firstGramDetSettings) q))
  have zG : uniformRect r r l.g z = G := by
    ext i j
    have off := rectOffset_lt i j
    exact zd _ (by omega) (Or.inl (by omega))
  have z15 : z.data 15=G.det⁻¹ := by simp [z,w]
  obtain ⟨t,k',hk',ei,val,fd,fi⟩ := uniformInverseTable_spec P z r l.g l.inv l.sub l.workA l.workB
    z0 z1 za zb z14 z31 z33 z35 z40 z41 z58 (by omega) gi (by omega) sa ab es.safe_end
    hp0 hp1 hpneg (by rw [zG]; exact z15) (by rw [zG]; intro i j; exact hbird (some (i,j)))
    (by rw [zG,z15]; exact hscaled)
  rw [zG] at val
  refine ⟨t,_,?_,eMove.seq (eDet.seq (er.seq (es.seq ei))),val,?_,?_⟩
  · unfold gramInverseTime; omega
  · intro q hq hdis hwork
    exact (fd q (by omega) hwork hdis).trans (zd q hq hwork)
  · intro q hq
    have hkeep : CofactorKeep q := by unfold CofactorKeep; omega
    exact (fi q hkeep).trans ((zi q (by omega)).trans (vFrame q hq))

end Geometry
end LinearProgramming
end Optimization
end OAI
