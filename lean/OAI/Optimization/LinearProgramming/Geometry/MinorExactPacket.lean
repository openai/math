import OAI.Optimization.LinearProgramming.Geometry.BorderProtocol
import OAI.Optimization.LinearProgramming.Contraction.MachineExchange
import OAI.Optimization.LinearProgramming.OracleSpec.IndexOrder

/-! Physical scalar entries and natural bounds of a complete sealed minor request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorInstall

open RAM OracleSpec OracleSpec.MinorLog Contraction.Machine

def matrixTag {r s n : ℕ} : RawIndex r s n → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem matrixTag_cases {r s n : ℕ} (u : RawIndex r s n) : matrixTag u=0 ∨ matrixTag u=1 := by cases u <;> simp [matrixTag]

theorem words_first {r s n : ℕ} (u : RawIndex r s n) : (words u)[0]?=some (matrixTag u) := by
  cases u <;> simp [matrixTag,words,squareWords]

theorem words_shape {r s n : ℕ} (u : RawIndex r s n) : (words u).length=2 ∨ 4 ≤ (words u).length := by
  cases u <;> simp only [words,squareWords_length] <;> omega

theorem words_short {r s n : ℕ} (u : RawIndex r s n) : (words u).length ≤ 2+2*n := by
  rcases u with a | a <;> (simp only [words,squareWords_length]; have := a.order.isLt; omega)

theorem scalar_packet {r s n : ℕ} (u : RawIndex r s n) (m : Memory ℚ)
    (request : registerPacket (m.atPC 0) 80 81=BorderBatch.packet u) :
    m.index 81=(words u).length ∧
    (∀ j, j < (words u).length → m.data (m.index 80+j)=(((words u)[j]?.getD 0 : ℕ):ℚ)) ∧
    m.data (m.index 80)=(matrixTag u:ℚ) := by
  have size : m.index 81=(words u).length := by
    simpa [registerPacket,Memory.atPC,BorderBatch.packet] using congrArg List.length request
  have entry (j : ℕ) (hj : j < (words u).length) :
      m.data (m.index 80+j)=(((words u)[j]?.getD 0 : ℕ):ℚ) := by
    have a : j < (registerPacket (m.atPC 0) 80 81).length := by simpa [registerPacket,Memory.atPC,size] using hj
    have b : j < (BorderBatch.packet u).length := by simpa [BorderBatch.packet] using hj
    have eq := congrArg (fun xs : List ℚ => xs[j]?) request
    change (registerPacket (m.atPC 0) 80 81)[j]?=(BorderBatch.packet u)[j]? at eq
    rw [List.getElem?_eq_getElem a,List.getElem?_eq_getElem b] at eq
    rw [List.getElem?_eq_getElem hj,Option.getD_some]
    simpa only [registerPacket,List.getElem_ofFn,Memory.atPC,BorderBatch.packet,List.getElem_map] using Option.some.inj eq
  have positive : 0 < (words u).length := by have := words_shape u; omega
  exact ⟨size,entry,by simpa [words_first] using entry 0 positive⟩

/-- Bounded integer request words have an input-independent encoding bound. -/
theorem nat_word_bits (i : ℕ) : ratBits (i:ℚ) ≤ i+3 := by
  simp only [ratBits,Rat.num_natCast,Int.natAbs_natCast,Rat.den_natCast,show Nat.log2 1=0 by rfl,Nat.add_zero]
  have := Nat.log2_le_self i
  omega

def directWidth (H r s n : ℕ) : ℕ := max H (r+s+n+4)

def directClock (r s n : ℕ) : ℕ := (2+2*n)*(5*(r+s+n+1)+32)+90

end MinorInstall
end Geometry
end LinearProgramming
end Optimization
end OAI
