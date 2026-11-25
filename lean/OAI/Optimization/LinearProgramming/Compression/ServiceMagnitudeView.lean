import OAI.Optimization.LinearProgramming.Compression.ServiceTableOrder
import OAI.Optimization.LinearProgramming.Compression.RequestIndex

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

variable {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}

/-- The final word of each stored slot is precisely the magnitude in the order used by
the commitment and request-lattice algorithms. -/
theorem Stored.generatorMagnitude {J : Finset (NonzeroPairMinor D E)} {s : Memory ℚ}
    (h : Stored D E J.sort s) (i : Fin J.card) :
    s.data (slotBase n i.val+stride n-1)=|pairMinorValue D E (J.orderEmbOfFin rfl i).val| := by
  have hi : i.val<J.sort.length := by simp
  have val := (h.slots ⟨i.val,hi⟩).magnitude
  have key : J.sort[i.val]=J.orderEmbOfFin rfl i := by
    simpa only [Finset.coe_orderIsoOfFin_apply] using get_sorted_eq_orderIso J i
  rw [key] at val
  simpa only [show slotBase n i.val+stride n-1=slotBase n i.val+2+2*n by unfold stride;omega] using val

/-- The compact tape passed to the logarithm, LLL and commitment routines. The next free
scalar address `F+g+1` is exported as well as the base `F`. -/
structure MagnitudeTape {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (J : Finset (NonzeroPairMinor D E)) (q : NonzeroPairMinor D E) (s : Memory ℚ) : Prop where
  base : s.index 5 = slotBase n (J.card+2)
  free : s.index 7 = slotBase n (J.card+2)+J.card+1
  values : ∀ i : Fin (J.card+1),s.data (s.index 5+i.val)=|pairMinorValue D E (requestIndices J q i).val|

/-- Every compact coordinate is a permissible input to the logarithm routine. -/
theorem MagnitudeTape.positive {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
    {J : Finset (NonzeroPairMinor D E)} {q : NonzeroPairMinor D E} {s : Memory ℚ}
    (h : MagnitudeTape D E J q s) (i : Fin (J.card+1)) : 0 < s.data (s.index 5+i.val) := by
  rw [h.values]
  exact abs_pos.mpr (requestIndices J q i).property

/-- Selecting the extra candidate after the stored table completes the exact graph-lattice
input vector, including the first request to an empty table. -/
theorem requestMagnitude {J : Finset (NonzeroPairMinor D E)} {s : Memory ℚ}
    (q : NonzeroPairMinor D E) (st : Stored D E J.sort s)
    (incoming : SlotAt D E q (slotBase n (J.card+1)) s) (i : Fin (J.card+1)) :
    s.data (slotBase n (if i.val<J.card then i.val else J.card+1)+stride n-1)=
      |pairMinorValue D E (requestIndices J q i).val| := by
  induction i using Fin.lastCases with
  | last =>
    simpa [show slotBase n (J.card+1)+stride n-1=slotBase n (J.card+1)+2+2*n by unfold stride;omega] using incoming.magnitude
  | cast i => simpa using st.generatorMagnitude i

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
