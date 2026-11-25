import OAI.Optimization.LinearProgramming.Geometry.UniformGramLayout
import OAI.Optimization.LinearProgramming.Elimination.Mask

/-! A single linear-time scalar/address-RAM loop applies a selected-coordinate mask in place. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM _root_.OAI.Optimization.LinearProgramming.Geometry

def vectorMaskCell : Block := .straight
  [.load 4 65,.load 5 66,.mul 5 4 5,.store 66 5,.incr 65 65,.incr 66 66]

private theorem vectorMaskCell_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K→Prop) (m : Memory K) (h66 : 7≤m.index 66) (hm : m.AllData P)
    (hv : P (m.data (m.index 65)*m.data (m.index 66))) :
    ∃t,Block.Eval (Memory.AllData P) vectorMaskCell m 6 t ∧
      t.data (m.index 66)=m.data (m.index 65)*m.data (m.index 66) ∧
      (∀p,7≤p → p≠m.index 66 → t.data p=m.data p) ∧ t.index 65=m.index 65+1 ∧
      t.index 66=m.index 66+1 ∧ ∀p,p≠65→p≠66→t.index p=m.index p := by
  let a := m.putData 4 (m.data (m.index 65))
  let b := a.putData 5 (a.data (a.index 66))
  let c := b.putData 5 (b.data 4*b.data 5)
  let d := c.putData (c.index 66) (c.data 5)
  let e := d.putIndex 65 (d.index 65+1)
  let t := e.putIndex 66 (e.index 66+1)
  have ea : Block.Eval (Memory.AllData P) (.op (.load 4 65)) m 1 a := Block.Eval.op_load _ _ _ hm (hm.putData _ (hm _))
  have eb : Block.Eval (Memory.AllData P) (.op (.load 5 66)) a 1 b := Block.Eval.op_load _ _ _ ea.safe_end (ea.safe_end.putData _ (ea.safe_end _))
  have hb : b.data 4*b.data 5=m.data (m.index 65)*m.data (m.index 66) := by
    simp [a,b,show m.index 66≠4 by omega]
  have ec : Block.Eval (Memory.AllData P) (.op (.mul 5 4 5)) b 1 c :=
    Block.Eval.op_mul _ _ _ _ eb.safe_end (eb.safe_end.putData _ (hb ▸ hv))
  have ed : Block.Eval (Memory.AllData P) (.op (.store 66 5)) c 1 d :=
    Block.Eval.op_store _ _ _ ec.safe_end (ec.safe_end.putData _ (ec.safe_end _))
  have ee : Block.Eval (Memory.AllData P) (.op (.incr 65 65)) d 1 e := Block.Eval.op_incr _ _ _ ed.safe_end ed.safe_end
  have et : Block.Eval (Memory.AllData P) (.op (.incr 66 66)) e 1 t := Block.Eval.op_incr _ _ _ ee.safe_end ee.safe_end
  refine ⟨t,ea.seq (eb.seq (ec.seq (ed.seq (ee.seq (et.seq (.skip et.safe_end)))))),?_,?_,by simp [t,e,d,c,b,a],by simp [t,e,d,c,b,a],?_⟩
  · simp [t,e,d,c,b,a,show m.index 66≠4 by omega]
  · intro p hp hne;simp [t,e,d,c,b,a,hne,show p≠4 by omega,show p≠5 by omega]
  · intro p hp hq;simp [t,e,d,c,b,a,hp,hq]

def uniformVectorMask : Block := .seq (indexMoves [(65,62),(66,63)]) (.forRange 19 50 vectorMaskCell)

theorem uniformVectorMask_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K→Prop) (m : Memory K) (n f v : ℕ) (S : Finset (Fin n)) (x : Fin n→K)
    (hn : m.index 50=n) (hf : m.index 62=f) (hv : m.index 63=v) (low : 7≤f) (sep : f+n≤v)
    (hm : m.AllData P) (h0 : P 0) (flagMem : ∀i : Fin n,m.data (f+i.val)=flag S i)
    (vecMem : ∀i : Fin n,m.data (v+i.val)=x i) :
    ∃ t c,c≤2+(n*(6+3)+2) ∧ Block.Eval (Memory.AllData P) uniformVectorMask m c t ∧
      (∀i : Fin n,t.data (v+i.val)=flag S i*x i) ∧
      (∀p,7≤p → (p<v ∨ v+n≤p) → t.data p=m.data p) ∧
      ∀p,p≠19→p≠65→p≠66→t.index p=m.index p := by
  let start := movedIndices m [(65,62),(66,63)]
  have es : Block.Eval (Memory.AllData P) (indexMoves [(65,62),(66,63)]) m 2 start := indexMoves_eval P m hm _
  let I (j : ℕ) (u : Memory K) := u.AllData P ∧ u.index 19=j ∧ u.index 65=f+j ∧ u.index 66=v+j ∧
    (∀p,p≠19→p≠65→p≠66→u.index p=m.index p) ∧
    (∀p,7≤p → (p<v ∨ v+j≤p) → u.data p=m.data p) ∧
    ∀i : Fin n,i.val<j → u.data (v+i.val)=flag S i*x i
  have ini : I 0 (start.putIndex 19 0) := by
    refine ⟨es.safe_end,by simp,by simp [start,movedIndices,hf],by simp [start,movedIndices,hv],?_,fun _ _ _=>rfl,fun _ h=>by omega⟩
    intro p p19 p65 p66; simp [start,movedIndices,p19,p65,p66]
  have adv (j : ℕ) (hj:j<n) (u : Memory K) (h : I j u) :
      ∃t k,k≤6 ∧ Block.Eval (Memory.AllData P) vectorMaskCell u k t ∧ I (j+1) (t.putIndex 19 (t.index 19+1)) := by
    let i : Fin n:=⟨j,hj⟩
    obtain ⟨us,u19,u65,u66,ui,ud,uv⟩ := h
    have uf : u.data (u.index 65)=flag S i := by rw [u65,ud _ (by omega) (Or.inl (by omega))];exact flagMem i
    have ux : u.data (u.index 66)=x i := by rw [u66,ud _ (by omega) (Or.inr le_rfl)];exact vecMem i
    have ok : P (u.data (u.index 65)*u.data (u.index 66)) := by
      rw [uf];by_cases hi:i∈S <;> simp [flag,hi,h0,us _]
    obtain ⟨t,et,val,frame,t65,t66,ti⟩ := vectorMaskCell_spec P u (by omega) us ok
    rw [uf,ux,u66] at val
    refine ⟨t,6,le_rfl,et,et.safe_end,by simp [ti 19 (by decide) (by decide),u19],
      by simp [t65,u65,Nat.add_assoc],by simp [t66,u66,Nat.add_assoc],?_,?_,?_⟩
    · intro p p19 p65 p66;exact (Memory.putIndex_ne _ p19 _).trans ((ti p p65 p66).trans (ui p p19 p65 p66))
    · intro p hp hr;exact (frame _ hp (by omega)).trans (ud _ hp (by omega))
    · intro k hk
      change t.data (v+k.val) = _
      by_cases hki : k.val=j
      · have he : k=i := Fin.ext hki; simpa only [he] using val
      · exact (frame _ (by omega) (by omega)).trans (uv k (by omega))
  obtain ⟨t,c,hc,et,done⟩ := Block.Eval.forRange_invariant (body:=vectorMaskCell) 19 50 n 6 I start
    es.safe_end ini (fun _ _ h=>⟨h.1,h.2.1,(h.2.2.2.2.1 50 (by decide) (by decide) (by decide)).trans hn⟩) adv
  exact ⟨t,2+c,Nat.add_le_add_left hc 2,es.seq et,fun i=>done.2.2.2.2.2.2 i i.isLt,done.2.2.2.2.2.1,done.2.2.2.2.1⟩

end Elimination
end LinearProgramming
end Optimization
end OAI
