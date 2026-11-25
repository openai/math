import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.Card

/-! # Counting exponent vectors in a multinomial expansion

The degree-`m` terms in a power of a finite sum are indexed by the functions
in `Finset.piAntidiag univ m`. The number of such profiles grows polynomially
in `m`, and each coefficient is bounded by the total number of words.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Placing every letter at a single index gives a degree profile. -/
theorem degreeProfiles_nonempty [Nonempty ι] (m : ℕ) :
    (piAntidiag (univ : Finset ι) m).Nonempty := by
  let i := Classical.arbitrary ι
  refine ⟨fun j ↦ if j = i then m else 0, ?_⟩
  simp

/-- Each entry of a degree profile lies between zero and its total degree. -/
theorem degreeProfiles_card_le (m : ℕ) :
    (piAntidiag (univ : Finset ι) m).card ≤ (m + 1) ^ Fintype.card ι := by
  let S := piAntidiag (univ : Finset ι) m
  let encode (k : S) (i : ι) : Fin (m + 1) :=
    ⟨k.val i, Nat.lt_succ_of_le (by
      rw [← (mem_piAntidiag.mp k.property).1]
      exact single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ i))⟩
  have h : Function.Injective encode := by
    intro k l hkl
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun hkl i)
  simpa [S] using Fintype.card_le_of_injective encode h

/-- Each multinomial coefficient counts a subset of the length-`m` words. -/
theorem multinomial_le_wordCount {m : ℕ} {k : ι → ℕ}
    (hk : k ∈ piAntidiag univ m) :
    Nat.multinomial univ k ≤ Fintype.card ι ^ m := by
  have htotal : Fintype.card ι ^ m = ∑ q ∈ piAntidiag (univ : Finset ι) m,
      Nat.multinomial univ q := by
    simpa using sum_pow_eq_sum_piAntidiag (univ : Finset ι) (fun _ ↦ (1 : ℕ)) m
  rw [htotal]
  exact single_le_sum (fun _ _ ↦ Nat.zero_le _) hk

end SpectralBooks
end LinearAlgebra
end OAI
