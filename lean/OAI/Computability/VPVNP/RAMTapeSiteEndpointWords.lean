import OAI.Computability.VPVNP.RAMTapeWordSlice
import OAI.Computability.VPVNP.RAMTapeUnaryWordValue

/-!
# Exact endpoint words for a processor's cost interval

A site numbered `v` with bucket capacity `2^e` checks the two endpoints
`v * 2^e` and `(v+1) * 2^e`. Padding the site address before incrementing it
retains the carry of the final site, whose end word equals the global cap.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteEndpoints

open BurstRAM TapeWord

variable {d : ℕ}

/-- Word encoding the start of the site’s cost interval, its address multiplied by the
power-of-two bucket capacity. -/
def startWord (e w : ℕ) (v : Word d) (h : d+e < w) : Word w :=
  ⟨v.val * 2^e, (Nat.mul_le_mul_right _ v.isLt.le).trans_lt
    ((pow_add 2 d e) ▸ Nat.pow_lt_pow_right (by decide : 1 < 2) h)⟩

/-- Word encoding the end of the site’s cost interval, `(v.val + 1) * 2^e` for site address
`v`. -/
def endWord (e w : ℕ) (v : Word d) (h : d+e < w) : Word w :=
  ⟨(v.val+1) * 2^e, (Nat.mul_le_mul_right _ v.isLt).trans_lt
    ((pow_add 2 d e) ▸ Nat.pow_lt_pow_right (by decide : 1 < 2) h)⟩

/-- Leave room for a carry out of the original address before shifting. -/
def padded (e w : ℕ) (v : Word d) := BurstRAM.wordBits v ++ List.replicate (w-(d+e)) false

@[simp] theorem padded_length (e w : ℕ) (v : Word d) (h : d+e < w) :
    (padded e w v).length = w-e := by simp [padded]; omega

theorem start_bits (e w : ℕ) (v : Word d) (h : d+e < w) :
    List.replicate e false ++ padded e w v = BurstRAM.wordBits (startWord e w v h) := by
  apply eq_of_length_value
  · simp only [List.length_append, List.length_replicate, padded_length _ _ _ h, length_wordBits]
    omega
  · simp [padded, startWord, value_append, value_wordBits, Nat.mul_comm]

theorem end_bits (e w : ℕ) (v : Word d) (h : d+e < w) :
    List.replicate e false ++ (UnaryWord.incScan true (padded e w v)).1 =
      BurstRAM.wordBits (endWord e w v h) := by
  have hv : value (padded e w v) = v.val := by simp [padded, value_append, value_wordBits]
  have room : v.val + 1 < 2^(w-e) := Nat.lt_of_le_of_lt v.isLt
    (Nat.pow_lt_pow_right (by decide) (by omega : d < w-e))
  apply eq_of_length_value
  · simp only [List.length_append, List.length_replicate, UnaryWord.incScan_length,
      padded_length _ _ _ h, length_wordBits]
    omega
  · rw [value_append, value_zeros, List.length_replicate, Nat.zero_add,
      UnaryWord.incScan_value_of_lt _ _ (by simpa [hv, padded_length _ _ _ h] using room), hv]
    simp [endWord, value_wordBits, Nat.mul_comm]

end RAMTape.SiteEndpoints

end VPVNP
end Computability
end OAI
