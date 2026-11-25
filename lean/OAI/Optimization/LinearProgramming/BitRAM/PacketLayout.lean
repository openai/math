import OAI.Optimization.LinearProgramming.BitRAM.Heap
import OAI.Optimization.LinearProgramming.RAM.ArrayFill
import OAI.Optimization.LinearProgramming.RAM.RAMCount

/-! The exact contiguous scalar packet shared by the two binary RAM conversions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

variable {K : Type*}

open RAM OracleSpec

/-- Every represented bit occupies one scalar cell in the order seen by the oracle. -/
def ScalarPacket [Zero K] [One K] (m : Memory K) (base : Nat) (bits : Word) : Prop :=
  ∀ i (hi : i < bits.length), m.data (base+i) = bitScalar bits[i]

namespace ScalarPacket

variable [Zero K] [One K] {m t : Memory K} {base : Nat} {bits : Word}

theorem nil (m : Memory K) (base : Nat) : ScalarPacket m base [] := by
  intro _ hi
  simp at hi

theorem snoc (h : ScalarPacket m base bits) (b : Bool)
    (last : m.data (base+bits.length) = bitScalar b) : ScalarPacket m base (bits ++ [b]) := by
  intro i hi
  by_cases before : i < bits.length
  · simpa [List.getElem_append_left before] using h i before
  · have eqi : i = bits.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using last

theorem congr (h : ScalarPacket m base bits) (eqv : ∀ i < bits.length,
    t.data (base+i) = m.data (base+i)) : ScalarPacket t base bits := by
  intro i hi
  exact (eqv i hi).trans (h i hi)

theorem map_data (h : ScalarPacket m base bits) :
    (List.range bits.length).map (fun i => m.data (base+i)) = bits.map bitScalar := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    have idx : i < bits.length := by simpa using hi
    simpa using h i idx

end ScalarPacket
end BitRAM
end LinearProgramming
end Optimization
end OAI
