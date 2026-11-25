import OAI.Optimization.LinearProgramming.RAM.Array

/-! Convert the validated designation scalar into two bounded RAM address cursors. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NativePrice

open RAM

private def designationStep : Block :=
  .seq (.op (.add 4 4 5)) (.seq (.op (.incr 14 14)) (.op (.incr 2 2)))

def designationBlock : Block :=
  .seq (.op (.const 4 0)) <| .seq (.op (.const 5 1)) <| .seq (.op (.addrConst 14 0)) <|
    .seq (.op (.addrCopy 2 9)) (.loop (.scalarLT 4 3) designationStep)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A designation less than the dimension takes at most five increments/comparisons
per coordinate. The scalar file and address bank outside the four listed cells survive. -/
theorem designationBlock_spec (P : K → Prop) (s : Memory K) (i : ℕ)
    (hs : s.AllData P) (hi : s.data 3=(i:K)) (hP : ∀ j : ℕ, j≤ i+1 → P (j:K)) :
    ∃ t, Block.Eval (Memory.AllData P) designationBlock s (5*i+5) t ∧
      t.index 14=i ∧ t.index 2=s.index 9+i ∧
      (∀ q, q≠4 → q≠5 → t.data q=s.data q) ∧
      ∀ q, q≠2 → q≠14 → t.index q=s.index q := by
  let a := s.putData 4 0
  let b := a.putData 5 1
  let c := b.putIndex 14 0
  let m := c.putIndex 2 (c.index 9)
  have h0 : P (0:K) := by simpa using hP 0 (by omega)
  have h1 : P (1:K) := by simpa using hP 1 (by omega)
  have ea : Block.Eval (Memory.AllData P) (.op (.const 4 0)) s 1 a := by
    simpa [a] using Block.Eval.op_const s 4 0 hs (hs.putData 4 (by simpa using h0 : P ((0:ℚ):K)))
  have eb : Block.Eval (Memory.AllData P) (.op (.const 5 1)) a 1 b := by
    simpa [b] using Block.Eval.op_const a 5 1 ea.safe_end
      (ea.safe_end.putData 5 (by simpa using h1 : P ((1:ℚ):K)))
  have ec := Block.Eval.op_addrConst b 14 0 eb.safe_end eb.safe_end
  have em := Block.Eval.op_addrCopy c 2 9 ec.safe_end ec.safe_end
  let I := fun (j : ℕ) (u : Memory K) => u.AllData P ∧ u.data 3=(i:K) ∧
    u.data 4=(j:K) ∧ u.data 5=1 ∧ u.index 14=j ∧ u.index 2=s.index 9+j ∧
    (∀ q, q≠4 → q≠5 → u.data q=s.data q) ∧ ∀ q, q≠2 → q≠14 → u.index q=s.index q
  have init : I 0 m := by
    refine ⟨em.safe_end,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [m,c,b,a] using hi
    · simp [m,c,b,a]
    · simp [m,c,b]
    · simp [m,c]
    · simp [m,c,b,a]
    · intro q h4 h5
      simp [m,c,b,a,h4,h5]
    · intro q h2 h14
      simp [m,c,b,a,h2,h14]
  have body (j : ℕ) (hj : j < i) (u : Memory K) (h : I j u) :
      (Cond.scalarLT 4 3).test u=true ∧ ∃ v,
        Block.Eval (Memory.AllData P) designationStep u 3 v ∧ I (j+1) v := by
    obtain ⟨safe,target,num,one,raw,atp,data,idx⟩ := h
    refine ⟨by simp [Cond.test,num,target,hj],?_⟩
    let x := u.putData 4 (u.data 4+u.data 5)
    let y := x.putIndex 14 (x.index 14+1)
    let v := y.putIndex 2 (y.index 2+1)
    have inc : u.data 4+u.data 5=((j+1:ℕ):K) := by simp [num,one]
    have ex := Block.Eval.op_add u 4 4 5 safe (safe.putData 4 (inc ▸ hP (j+1) (by omega)))
    have ey := Block.Eval.op_incr x 14 14 ex.safe_end ex.safe_end
    have ev := Block.Eval.op_incr y 2 2 ey.safe_end ey.safe_end
    refine ⟨v,ex.seq (ey.seq ev),ev.safe_end,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [v,y,x] using target
    · simpa [v,y,x] using inc
    · simpa [v,y,x] using one
    · simp [v,y,x,raw]
    · simp [v,y,x,atp,Nat.add_assoc]
    · intro q h4 h5
      simpa [v,y,x,h4] using data q h4 h5
    · intro q h2 h14
      simpa [v,y,x,h2,h14] using idx q h2 h14
  have stop (u : Memory K) (h : I i u) :
      (Cond.scalarLT 4 3).test u=false ∧ u.AllData P :=
    ⟨by simp [Cond.test,h.2.1,h.2.2.1],h.1⟩
  obtain ⟨t,e,_,_,_,_,raw,atp,data,idx⟩ :=
    Block.Eval.loop_invariant_exact I m i 3 init body stop
  refine ⟨t,?_,raw,atp,data,idx⟩
  simpa only [designationBlock,show 1+(1+(1+(1+(i*(3+2)+1))))=5*i+5 by omega] using
    ea.seq (eb.seq (ec.seq (em.seq e)))

end NativePrice
end LinearProgramming
end Optimization
end OAI
