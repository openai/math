import OAI.Optimization.LinearProgramming.Compression.SignWireHighShell
import OAI.Optimization.LinearProgramming.Compression.SignWireWindow

/-! The physical return ports share their window-frame certificate between
rational and general ordered-field numerical callbacks. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM RAM.Callable

/-- The nested return writes only low numeric and VM routing words. It therefore
agrees with the returned ideal storage on the full high window, including all
cache locations, and retains doubled addresses outside that window. -/
theorem returned_shell {K : Type*} (stage last caller : Memory K) (cap base p tag : ℕ) :
    HighShell ((Call.pack (windowMemory cap (evenView stage)
      (((Odd.memory last caller).putIndex 0 3).putIndex 2 5)) (Call.savedOddFrame stage)).putIndex 14 tag)
      last caller cap base p := by
  constructor
  · intro i _ hi _
    simp only [Memory.putIndex_data,Call.data_even,windowMemory,hi,ite_true]
  · intro i low hi
    rw [Memory.putIndex_ne _ (by omega : 2*i≠14) _,Call.index_even]
    simp only [windowMemory,hi,ite_true,Memory.putIndex_ne _ (by omega : i≠2),
      Memory.putIndex_ne _ (by omega : i≠0)]
  · intro i low
    rw [Memory.putIndex_ne _ (by omega : 2*i≠14) _,Call.index_even]
    omega

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
