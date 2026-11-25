import OAI.Optimization.LinearProgramming.Lattice.BitSwapRead
import OAI.Optimization.LinearProgramming.Lattice.BitSwapPacking

/-! Pack all the native coefficient rows after the adjacent swap. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open Hex.Internal

theorem swapNuMatrix_packState {n m : ℕ} (s : LLLState n m) (k : Fin n) (hk : 0 < k.val) :
    (List.range (packMatrix s.ν).length).map (swapNuRow k.val (packState s)) =
      packMatrix (s.swapStep k.val).ν := by
  simp only [length_packMatrix]
  apply eq_packed_of_rows _ _ (by simp)
  intro i
  have row : swapNuRow k.val (packState s) i.val = packVector ((s.swapStep k.val).ν.getRow i) := by
    change (List.range (rowAt (packMatrix s.ν) i.val).length).map _ = _
    rw [rowAt_packMatrix,length_packVector]
    apply List.ext_getElem
    · simp
    · intro j _ hj
      have h : j<n := by simpa using hj
      simpa [packVector] using swapNuEntry_native s k hk i ⟨j,h⟩
  simpa [rowAt,readAt,i.isLt] using row


end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
