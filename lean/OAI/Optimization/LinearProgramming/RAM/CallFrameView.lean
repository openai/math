import OAI.Optimization.LinearProgramming.RAM.CallMemory

/-! Recover the caller frame from the odd addresses of a prepared physical register file. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

variable {K : Type*}

/-- Registers preserved by an isolated call, in their original frame numbering. -/
def savedOddFrame (m : Memory K) : Memory K where
  data j := m.data (2*j+1)
  index j := m.index (2*j+1)

/-- Matching the virtual scalar data and the doubled virtual addresses at every even location
suffices to invoke the callee with the caller's actual odd register file. -/
theorem eq_pack_of_even (m v : Memory K)
    (hd : ∀ j, m.data (2*j) = v.data j)
    (hi : ∀ j, m.index (2*j) = 2*v.index j) : m = pack v (savedOddFrame m) := by
  have split (P : Nat → Prop) (he : ∀ j, P (2*j)) (ho : ∀ j, P (2*j+1)) (i : Nat) : P i := by
    by_cases h : i % 2 = 0
    · convert he (i/2) using 1; omega
    · convert ho (i/2) using 1; omega
  have data : m.data = (pack v (savedOddFrame m)).data := funext (split _
    (fun j => (hd j).trans (data_even v (savedOddFrame m) j).symm)
    (fun j => (data_odd v (savedOddFrame m) j).symm))
  have index : m.index = (pack v (savedOddFrame m)).index := funext (split _
    (fun j => (hi j).trans (index_even v (savedOddFrame m) j).symm)
    (fun j => (index_odd v (savedOddFrame m) j).symm))
  cases m
  exact congrArg₂ Memory.mk data index

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
