import OAI.Optimization.LinearProgramming.NativePrice.Tape

/-! Forward scan of the paired continuation markers of a framed natural. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NativePrice

open RAM OracleSpec

private def scanBody : Block :=
  .seq (.op (.incr 3 3)) (.seq (.op (.incr 3 3)) (.op (.load 4 3)))

def scanBlock : Block :=
  .seq (.op (.const 6 0)) (.seq (.op (.load 4 3)) (.loop (.scalarLT 6 4) scanBody))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem scanBlock_spec (P : K → Prop) (s : Memory K) (base : ℕ) (bs : Word)
    (hc : s.index 3=base) (hbase : 9 ≤ base) (hw : WordAt s base (frame bs))
    (hm : s.AllData P) (hzero : P 0) :
    ∃ t, Block.Eval (Memory.AllData P) scanBlock s (5*bs.length+3) t ∧
      t.index 3=base+2*bs.length ∧
      (∀ p, p≠4 → p≠6 → t.data p=s.data p) ∧
      ∀ p, p≠3 → t.index p=s.index p := by
  obtain ⟨markers,_⟩ := frame_cells s base bs hw
  let z := s.putData 6 0
  let m := z.putData 4 (z.data (z.index 3))
  have ez : Block.Eval (Memory.AllData P) (.op (.const 6 0)) s 1 z := by
    simpa [z] using Block.Eval.op_const s 6 0 hm (hm.putData 6 (by simpa using hzero : P ((0:ℚ):K)))
  have em := Block.Eval.op_load z 4 3 ez.safe_end (ez.safe_end.putData 4 (ez.safe_end _))
  let I := fun (j : ℕ) (u : Memory K) => u.AllData P ∧ u.index 3=base+2*j ∧
    u.data 6=0 ∧ u.data 4=(if j<bs.length then 1 else 0) ∧
    (∀ p, p≠4 → p≠6 → u.data p=s.data p) ∧ ∀ p, p≠3 → u.index p=s.index p
  have init : I 0 m := by
    refine ⟨em.safe_end,?_,?_,?_,?_,?_⟩
    · simp [m,z,hc]
    · simp [m,z]
    · simpa [m,z,hc,show base≠6 by omega] using markers 0 (Nat.zero_le _)
    · intro p h4 h6
      simp [m,z,h4,h6]
    · intro p _
      rfl
  have body (j : ℕ) (hj : j<bs.length) (u : Memory K) (h : I j u) :
      (Cond.scalarLT 6 4).test u=true ∧ ∃ v,
        Block.Eval (Memory.AllData P) scanBody u 3 v ∧ I (j+1) v := by
    obtain ⟨safe,cur,zero,flag,data,idx⟩ := h
    refine ⟨by simp [Cond.test,zero,flag,hj],?_⟩
    let u1 := u.putIndex 3 (u.index 3+1)
    let u2 := u1.putIndex 3 (u1.index 3+1)
    let v := u2.putData 4 (u2.data (u2.index 3))
    have e1 := Block.Eval.op_incr u 3 3 safe safe
    have e2 := Block.Eval.op_incr u1 3 3 e1.safe_end e1.safe_end
    have e3 := Block.Eval.op_load u2 4 3 e2.safe_end (e2.safe_end.putData 4 (e2.safe_end _))
    have pos : u2.index 3=base+2*(j+1) := by simp [u2,u1,cur]; omega
    refine ⟨v,e1.seq (e2.seq e3),e3.safe_end,pos,by simpa [v,u2,u1] using zero,?_,?_,?_⟩
    · change (u2.putData 4 _).data 4=_
      rw [Memory.putData_same,pos]
      exact (data _ (by omega) (by omega)).trans (markers (j+1) hj)
    · intro p h4 h6
      simpa [v,u2,u1,h4] using data p h4 h6
    · intro p hp
      simpa [v,u2,u1,hp] using idx p hp
  have stop (u : Memory K) (h : I bs.length u) :
      (Cond.scalarLT 6 4).test u=false ∧ u.AllData P :=
    ⟨by simp [Cond.test,h.2.2.1,h.2.2.2.1],h.1⟩
  obtain ⟨t,e,_,cur,_,_,data,idx⟩ :=
    Block.Eval.loop_invariant_exact I m bs.length 3 init body stop
  refine ⟨t,?_,cur,data,idx⟩
  simpa only [scanBlock,show 1+(1+(bs.length*(3+2)+1))=5*bs.length+3 by omega] using
    ez.seq (em.seq e)

end NativePrice
end LinearProgramming
end Optimization
end OAI
