import OAI.Optimization.LinearProgramming.NativePrice.Tape

/-! Recover one little-endian payload by walking backwards and evaluating Horner's rule. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NativePrice

open RAM OracleSpec

private def hornerBody : Block :=
  .seq (.op (.decr 4 4)) <| .seq (.op (.load 5 4)) <| .seq (.op (.add 3 3 3)) <|
    .seq (.op (.add 3 3 5)) (.op (.decr 4 4))

def hornerBlock : Block := .seq (.op (.const 3 0)) (.loop (.addrLT 5 4) hornerBody)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem hornerBlock_spec (P : K → Prop) (s : Memory K) (base : ℕ) (bs : Word)
    (hstart : s.index 5=base) (hend : s.index 4=base+2*bs.length) (hbase : 9 ≤ base)
    (hw : WordAt s base (frame bs)) (hm : s.AllData P)
    (hv : ∀ x : ℕ, x ≤ 2^bs.length → P (x:K)) :
    ∃ t, Block.Eval (Memory.AllData P) hornerBlock s (7*bs.length+2) t ∧
      t.data 3=(value bs:K) ∧ (∀ p, p≠3 → p≠5 → t.data p=s.data p) ∧
      ∀ p, p≠4 → t.index p=s.index p := by
  obtain ⟨_,digits⟩ := frame_cells s base bs hw
  let m := s.putData 3 0
  have h0 : P (0:K) := by simpa using hv 0 (Nat.zero_le _)
  have ez : Block.Eval (Memory.AllData P) (.op (.const 3 0)) s 1 m := by
    simpa [m] using Block.Eval.op_const s 3 0 hm
      (hm.putData 3 (by simpa using h0 : P ((0:ℚ):K)))
  let I := fun (j : ℕ) (u : Memory K) => u.AllData P ∧ u.index 5=base ∧
    u.index 4=base+2*(bs.length-j) ∧ u.data 3=(value (bs.drop (bs.length-j)) : K) ∧
    (∀ p, p≠3 → p≠5 → u.data p=s.data p) ∧ ∀ p, p≠4 → u.index p=s.index p
  have init : I 0 m := by
    refine ⟨ez.safe_end,hstart,?_,?_,?_,?_⟩
    · simpa [m] using hend
    · simp [m,value]
    · intro p hp _
      simp [m,hp]
    · intro p _
      rfl
  have body (j : ℕ) (hj : j<bs.length) (u : Memory K) (h : I j u) :
      (Cond.addrLT 5 4).test u=true ∧
        ∃ v, Block.Eval (Memory.AllData P) hornerBody u 5 v ∧ I (j+1) v := by
    obtain ⟨safe,left,right,acc,data,idx⟩ := h
    let p := bs.length-(j+1)
    have plen : p<bs.length := by dsimp [p]; omega
    have pred : bs.length-j=p+1 := by dsimp [p]; omega
    have trip : base<u.index 4 := by omega
    refine ⟨by simp [Cond.test,left,trip],?_⟩
    let a := u.putIndex 4 (u.index 4-1)
    let b := a.putData 5 (a.data (a.index 4))
    let c := b.putData 3 (b.data 3+b.data 3)
    let d := c.putData 3 (c.data 3+c.data 5)
    let v := d.putIndex 4 (d.index 4-1)
    have ea := Block.Eval.op_decr u 4 4 safe safe
    have eb := Block.Eval.op_load a 5 4 ea.safe_end (ea.safe_end.putData 5 (ea.safe_end _))
    have pos : a.index 4 = base+2*p+1 := by simp [a,right,pred]; omega
    have bit : b.data 5 = (bs[p].toNat:K) := by
      rw [show b.data 5 = a.data (a.index 4) from Memory.putData_same ..,pos]
      exact (data _ (by omega) (by omega)).trans (digits p plen)
    have dbl : b.data 3+b.data 3=((2*value (bs.drop (p+1)) : ℕ):K) := by
      simp [b,a,acc,pred,two_mul]
    have next : c.data 3+c.data 5=(value (bs.drop p):K) := by
      rw [value_drop_step bs p plen]
      simp [c,dbl,bit]
    have bound : value (bs.drop p) ≤ 2^bs.length := by
      exact (value_lt _).le.trans (Nat.pow_le_pow_right (by decide) (by simp))
    have bound2 : 2*value (bs.drop (p+1)) ≤ 2^bs.length := by
      rw [value_drop_step bs p plen] at bound
      omega
    have ec := Block.Eval.op_add b 3 3 3 eb.safe_end
      (eb.safe_end.putData _ (dbl ▸ hv _ bound2))
    have ed := Block.Eval.op_add c 3 3 5 ec.safe_end
      (ec.safe_end.putData _ (next ▸ hv _ bound))
    have ev := Block.Eval.op_decr d 4 4 ed.safe_end ed.safe_end
    refine ⟨v,ea.seq (eb.seq (ec.seq (ed.seq ev))),ev.safe_end,?_,?_,?_,?_,?_⟩
    · simpa [v,d,c,b,a] using left
    · change v.index 4=base+2*p
      simp [v,d,c,b,pos]
    · simpa [v,d] using next
    · intro q h3 h5
      simpa [v,d,c,b,a,h3,h5] using data q h3 h5
    · intro q h4
      simpa [v,d,c,b,a,h4] using idx q h4
  have stop (u : Memory K) (h : I bs.length u) :
      (Cond.addrLT 5 4).test u=false ∧ u.AllData P :=
    ⟨by simp [Cond.test,h.2.1,h.2.2.1],h.1⟩
  obtain ⟨t,e,_,_,_,out,data,idx⟩ := Block.Eval.loop_invariant_exact I m bs.length 5 init body stop
  refine ⟨t,?_,by simpa using out,data,idx⟩
  simpa only [hornerBlock,show 1+(bs.length*(5+2)+1)=7*bs.length+2 by omega] using ez.seq e

end NativePrice
end LinearProgramming
end Optimization
end OAI
