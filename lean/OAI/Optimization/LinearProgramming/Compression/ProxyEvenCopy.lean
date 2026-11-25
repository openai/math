import OAI.Optimization.LinearProgramming.RAM.StrideCopy

/-! Copy the numerical magnitudes from the saved odd bank to their even virtual inputs. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceFill

open RAM

/-- Even scalar zero temporarily protects scalar one. Copying the tail first
also handles a source vector beginning at physical address one. -/
def copyEvenInput : Block :=
  .seq (.op (.copy 0 1)) <| .seq (StrideCopy.block false 13 15 17 105 1 2 2) <|
    .seq (.op (.copy 1 0)) (.op (.load 0 11))

theorem copyEvenInput_eval {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (F g : ℕ)
    (base : s.index 11 = 2*F+1) (src : s.index 13 = 2*F+3)
    (dst : s.index 15 = 2) (size : s.index 105 = g) (hs : s.AllData P) :
    ∃ t, Block.Eval (Memory.AllData P) copyEvenInput s (9*g+5) t ∧
      (∀ i ≤ g, t.data (2*i) = s.data (2*(F+i)+1)) ∧
      (∀ i, t.data (2*i+1) = s.data (2*i+1)) ∧
      (∀ i, g < i → t.data (2*i) = s.data (2*i)) ∧
      ∀ j, j ≠ 13 → j ≠ 15 → j ≠ 17 → t.index j = s.index j := by
  let a := s.putData 0 (s.data 1)
  have ea : Block.Eval (Memory.AllData P) (.op (.copy 0 1)) s 1 a :=
    Block.Eval.op_copy s 0 1 hs (hs.putData _ (hs _))
  have a13 : a.index 13 = 2*F+3 := src
  have a15 : a.index 15 = 2 := dst
  obtain ⟨c,ec,cp,fr,_,_,_,addr⟩ :=
    StrideCopy.block_correct P a false 13 15 17 105 1 2 2 g ea.safe_end size
      (by decide) (by decide) (by simp)
      (by intro j _; simp only [StrideCopy.address_forward,a13]; omega)
      (by intro j _; simp only [StrideCopy.address_forward,a15]; omega)
      (by intro i j _ _; simp only [StrideCopy.address_forward,a13,a15]; omega)
  have frame (r : ℕ) (h : r ≠ 1) (away : ∀ j < g, r ≠ 2+2*j) : c.data r = a.data r :=
    fr r h (by simpa only [StrideCopy.address_forward,a15] using away)
  have c0 : c.data 0 = s.data 1 :=
    (frame 0 (by decide) (by intro j _; omega)).trans (Memory.putData_same _ _ _)
  let b := c.putData 1 (s.data 1)
  have eb : Block.Eval (Memory.AllData P) (.op (.copy 1 0)) c 1 b := by
    simpa only [b,c0] using Block.Eval.op_copy c 1 0 ec.safe_end (ec.safe_end.putData _ (ec.safe_end _))
  have odd (i : ℕ) : b.data (2*i+1) = s.data (2*i+1) := by
    by_cases hit : 2*i+1 = 1
    · rw [hit]; exact Memory.putData_same _ _ _
    · exact (Memory.putData_ne c hit _).trans ((frame _ hit (by intro j _; omega)).trans
        (Memory.putData_ne s (by omega : 2*i+1 ≠ 0) _))
  have b11 : b.index 11 = 2*F+1 := (addr 11 (by decide) (by decide) (by decide)).trans base
  let t := b.putData 0 (s.data (2*F+1))
  have et : Block.Eval (Memory.AllData P) (.op (.load 0 11)) b 1 t := by
    simpa only [t,b11,odd] using
      Block.Eval.op_load b 0 11 eb.safe_end (eb.safe_end.putData _ (eb.safe_end _))
  refine ⟨t, ?_, ?_, ?_, ?_, fun j a b c => addr j a b c⟩
  · rw [show 9*g+5 = 1+(g*(2+2+5)+2+(1+1)) by omega]
    exact ea.seq (ec.seq (eb.seq et))
  · intro i hi
    cases i with
    | zero => simp [t]
    | succ j =>
      have hj : j < g := by omega
      have val := cp j hj
      simp only [StrideCopy.address_forward,a13,a15] at val
      rw [show 2*(j+1) = 2+2*j by omega, show 2*(F+(j+1))+1 = 2*F+3+2*j by omega]
      exact (Memory.putData_ne b (by omega : 2+2*j ≠ 0) _).trans
        ((Memory.putData_ne c (by omega : 2+2*j ≠ 1) _).trans
          (val.trans (Memory.putData_ne s (by omega : 2*F+3+2*j ≠ 0) _)))
  · intro i
    exact (Memory.putData_ne b (by omega : 2*i+1 ≠ 0) _).trans (odd i)
  · intro i hi
    exact (Memory.putData_ne b (by omega : 2*i ≠ 0) _).trans
      ((Memory.putData_ne c (by omega : 2*i ≠ 1) _).trans
        ((frame _ (by omega) (by intro j hj; omega)).trans
          (Memory.putData_ne s (by omega : 2*i ≠ 0) _)))

end ServiceFill
end Compression
end LinearProgramming
end Optimization
end OAI
