import OAI.LinearAlgebra.SpectralBooks.WireIdentity

namespace OAI
/-! # Repetition of a finite wire tile

Independent copies expand into a sum over words of tile selectors. A
restriction on the residual wires can be tensored with every term.
-/

open scoped BigOperators Classical

namespace LinearAlgebra.SpectralBooks.ChordGraph

open SiteTensor

variable {k : ℕ} [Nonempty (Fin k)] (K : Type*) [Field K]

/-- Repeat an ordinary sum of local wire restrictions on `t` disjoint blocks,
and route a final residual block by the restriction `hr`. The selectors
are precisely the words of length `t` in the original selector alphabet. -/
theorem repeat_wire_tile (a r rSupply : Widths k) (t : ℕ)
    {J : Type*} [Fintype J] (U : J → Widths k)
    (z : J → (∀ i, (raw K a).Leg i) → K)
    (hz : (raw K a).coeff = ∑ j, z j)
    (hU : ∀ j, ({raw K a with coeff := z j} : Raw (Fin k) K).Restricts (raw K (U j)))
    (hr : (raw K r).Restricts (raw K rSupply)) :
    let T := raw K (t • a + r)
    ∃ c : (Fin t → J) → (∀ i, T.Leg i) → K,
      T.coeff = ∑ w, c w ∧ ∀ w, ({T with coeff := c w} : Raw (Fin k) K).Restricts
        (raw K ((∑ i, U (w i)) + rSupply)) := by
  have tile : graphClass K a ≤ ∑ j, graphClass K (U j) := by
    rw [← ofRaw_raw]
    calc
      ofRaw (raw K a) ≤ ∑ j, ofRaw ({raw K a with coeff := z j} : Raw (Fin k) K) := by
        change ofCoeffs (raw K a).coeff ≤ ∑ j, ofCoeffs (z j)
        rw [hz]
        exact ordinary_sum_le z
      _ ≤ _ := Finset.sum_le_sum fun j _ => (ofRaw_le_iff.mpr (hU j)).trans_eq (ofRaw_raw K (U j))
  have remainder : graphClass K r ≤ graphClass K rSupply := by
    simpa only [ofRaw_raw] using (ofRaw_le_iff.mpr hr)
  have compare : ofRaw (raw K (t • a + r)) ≤
      ∑ w : Fin t → J, graphClass K ((∑ i, U (w i)) + rSupply) := by
    rw [ofRaw_raw, graphClass_add, graphClass_nsmul]
    refine (mul_mono (pow_le_pow_left' tile t) remainder).trans_eq ?_
    simp_rw [graphClass_add, graphClass_sum]
    rw [← Finset.sum_mul, ← Fintype.prod_sum (fun (_ : Fin t) (j : J) => graphClass K (U j))]
    simp
  obtain ⟨c, hc, himages⟩ := images_of_le_sum (raw K (t • a + r)) _ compare
  exact ⟨c, hc, fun w => ofRaw_le_iff.mp ((himages w).trans_eq (ofRaw_raw K _).symm)⟩

end LinearAlgebra.SpectralBooks.ChordGraph

end OAI
