import OAI.Optimization.LinearProgramming.NormalSubspace.Spec
import OAI.Optimization.LinearProgramming.Geometry.GramEntries

/-! The scalar length of the ordinary complementary matrix pair, before the marked call starts. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace

open Matrix RAM OracleSpec Geometry
open scoped Matrix

theorem gramEntries {r n : ℕ} (M : Matrix (Fin r) (Fin n) ℚ) : encodedGramInput M=MinorLog.entries M :=
  Geometry.encodedGramInput_eq_entries M

private theorem entry_bits {r n b : ℕ} (M : Matrix (Fin r) (Fin n) ℚ) (h : ∀i j,ratBits (M i j) ≤ b) :
    ∀ z∈MinorLog.entries M,ratBits z ≤ b := by
  intro z hz
  obtain ⟨row,hr,entry⟩:=List.mem_flatten.mp hz
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hr
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp entry
  exact h i j

private theorem bits_sum (xs : List ℚ) (b : ℕ) (h : ∀z∈xs,ratBits z ≤ b) : (xs.map ratBits).sum ≤ xs.length*b := by
  induction xs with
  | nil => simp
  | cons z tail ih =>
    have hz:=h z List.mem_cons_self
    have rest:=ih (fun a ha=>h a (List.mem_cons_of_mem _ ha))
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm b] using Nat.add_le_add hz rest

theorem inputSize_le {r s b : ℕ} (D : Matrix (Fin r) (Fin (r+s)) ℚ) (E : Matrix (Fin s) (Fin (r+s)) ℚ)
    (hd : ∀i j,ratBits (D i j) ≤ b) (he : ∀i j,ratBits (E i j) ≤ b) : inputSize D E ≤ r+s+(r+s)^2*b := by
  have all:=bits_sum (MinorLog.entries D++MinorLog.entries E) b (by
    intro z hz;rcases List.mem_append.mp hz with h|h
    · exact entry_bits D hd _ h
    · exact entry_bits E he _ h)
  have len : (MinorLog.entries D++MinorLog.entries E).length=(r+s)^2 := by
    simp only [←gramEntries,List.length_append,length_encodedGramInput,pow_two,Nat.add_mul]
  unfold inputSize;rw [len] at all;omega

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
