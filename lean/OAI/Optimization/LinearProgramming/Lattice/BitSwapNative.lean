import OAI.Optimization.LinearProgramming.Lattice.BitSwapNuPacked
import OAI.Optimization.LinearProgramming.Lattice.BitArithmeticBridge

/-! Equivalence of all three tables before and after an adjacent LLL swap. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open Hex.Internal

theorem swapStep_packState {n m : ℕ} (s : LLLState n m) (k : ℕ) :
    swapStep k (packState s) = packState (s.swapStep k) := by
  by_cases hkn : k<n
  · by_cases hp : 0<k
    · let f : Fin n := ⟨k,hkn⟩
      let p := Hex.GramSchmidt.prevRow f hp
      let g := gramQuad k (packState s)
      have hb : (s.swapStep k).b = Hex.Matrix.rowSwap s.b p f := by
        unfold LLLState.swapStep
        rw [dite_eq_left hkn,dite_eq_left hp]
        rfl
      have hd : (s.swapStep k).d = s.d.set k (swappedGram g) := by
        unfold LLLState.swapStep
        rw [dite_eq_left hkn,dite_eq_left hp]
        rw [swappedGram_native,show g = _ from gramQuad_packState s f hp]
        dsimp only
        let dn : ℤ := s.d.get ⟨k+1,by omega⟩
        let dp : ℤ := s.d.get ⟨p.val,by omega⟩
        let dk : ℤ := s.d.get ⟨k,by omega⟩
        let v := (s.ν.getRow f).get p
        exact congrArg (fun t : ℤ => s.d.set k ((t+v^2)/dk).toNat) (mul_comm dn dp)
      have hB : swapRows (k-1) k (packMatrix s.b) = packMatrix (s.swapStep k).b := by
        rw [hb]; exact swapRows_packMatrix s.b p f
      have hD : (packVector s.d).set k (swappedGram g) = packVector (s.swapStep k).d := by
        rw [hd]; exact packVector_set s.d ⟨k,by omega⟩ _
      have active : 0<k ∧ k<(packState s).1.length := ⟨hp,by simpa [packState] using hkn⟩
      rw [swapStep,ite_eq_left active]
      exact congrArg₂ Prod.mk hB (congrArg₂ Prod.mk (swapNuMatrix_packState s f hp) hD)
    · have inactive : ¬(0 < k ∧ k < (packState s).1.length) := fun h => hp h.1
      have unchanged : s.swapStep k=s := by
        unfold LLLState.swapStep
        rw [dite_eq_left hkn,dite_eq_right hp]
      rw [swapStep,ite_eq_right inactive,unchanged]
  · have inactive : ¬(0 < k ∧ k < (packState s).1.length) := by simp [packState,hkn]
    have unchanged : s.swapStep k=s := by
      unfold LLLState.swapStep
      rw [dite_eq_right hkn]
    rw [swapStep,ite_eq_right inactive,unchanged]

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
