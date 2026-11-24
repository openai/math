import OAI.Computability.VPVNP.SpectralLocalizationCone

/-!
# Removing additive slack in strict spectral comparison

Appendix A.1 obtains a comparison with a common summand after clearing
denominators. Trading multiple copies absorbs that summand and leaves a
single multiplicative catalyst. Its size bounds the number of copies needed
for all tensor powers simultaneously.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

variable {S : Type*} [CommSemiring S] [Preorder S] (H : OrderBounds S)
include H

private theorem copy_trade {u v w : S} (h : u + w ≤ v + w) (q : ℕ) :
    (q : S) * u + w ≤ (q : S) * v + w := by
  induction q with
  | zero => simp
  | succ q ih =>
    calc
      _ = (q : S) * u + (u + w) := by push_cast; ring
      _ ≤ (q : S) * u + (v + w) := H.add_mono le_rfl h
      _ = v + ((q : S) * u + w) := by ring
      _ ≤ v + ((q : S) * v + w) := H.add_mono le_rfl ih
      _ = _ := by push_cast; ring

private theorem one_le_product {u v : S} (hu : 1 ≤ u) (hv : 1 ≤ v) : 1 ≤ u * v :=
  hu.trans (by simpa using H.mul_mono u hv)

private theorem one_le_succ (n : ℕ) : (1 : S) ≤ (n : S) + 1 := by
  simpa using H.add_mono (H.zero_le (n : S)) (le_rfl (a := (1 : S)))

/-- A common summand in the comparison between `(b+1)cX` and `bcY` can
be traded away by taking `q` copies, with `q c Y` large enough to cover it. -/
theorem remove_additive_slack {x y c w : S} (hc : c ≠ 0) (hy : y ≠ 0) (b : ℕ)
    (h : c * (((b : S) + 1) * x) + w ≤ c * ((b : S) * y) + w) :
    ∃ D : S, 1 ≤ D ∧ D * x ≤ D * y := by
  obtain ⟨r, hr⟩ := H.bounded w
  let q := r + 1
  have hq : (1 : S) ≤ q := by simpa [q] using one_le_succ H r
  have hcy := one_le_product H (H.one_le hc) (H.one_le hy)
  have hw : w ≤ (q : S) * (c * y) := calc
    w ≤ (r : S) := hr
    _ ≤ (q : S) := by simpa [q] using H.add_mono (le_rfl (a := (r : S))) (H.zero_le 1)
    _ ≤ _ := by simpa using H.mul_mono (q : S) hcy
  let D := (q : S) * ((b : S) + 1) * c
  refine ⟨D, one_le_product H (one_le_product H hq (one_le_succ H b)) (H.one_le hc), ?_⟩
  calc
    D * x = (q : S) * (c * (((b : S) + 1) * x)) := by dsimp [D]; ring
    _ ≤ (q : S) * (c * (((b : S) + 1) * x)) + w := by
      simpa using H.add_mono (le_rfl (a := (q : S) * (c * (((b : S) + 1) * x)))) (H.zero_le w)
    _ ≤ (q : S) * (c * ((b : S) * y)) + w := copy_trade H h q
    _ ≤ (q : S) * (c * ((b : S) * y)) + (q : S) * (c * y) := H.add_mono le_rfl hw
    _ = D * y := by dsimp [D]; ring

/-- The same catalyst can be reused once per factor of a tensor power. -/
theorem catalyst_powers {x y D : S} (h : D * x ≤ D * y) (m : ℕ) :
    D * x ^ m ≤ D * y ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      D * x ^ (m + 1) = x ^ m * (D * x) := by rw [pow_succ]; ring
      _ ≤ x ^ m * (D * y) := H.mul_mono _ h
      _ = y * (D * x ^ m) := by ring
      _ ≤ y * (D * y ^ m) := H.mul_mono _ ih
      _ = D * y ^ (m + 1) := by rw [pow_succ]; ring

/-- The catalyst is bounded by a natural number independent of the power. -/
theorem catalyst_uniform_bound {x y D : S} (hD : 1 ≤ D) (h : D * x ≤ D * y) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ m : ℕ, x ^ m ≤ (K : S) * y ^ m := by
  obtain ⟨r, hr⟩ := H.bounded D
  refine ⟨r + 1, by omega, ?_⟩
  intro m
  calc
    x ^ m ≤ D * x ^ m := by simpa [mul_comm] using H.mul_mono (x ^ m) hD
    _ ≤ D * y ^ m := catalyst_powers H h m
    _ ≤ (r : S) * y ^ m := by simpa [mul_comm] using H.mul_mono (y ^ m) hr
    _ ≤ _ := by
      have hsucc : (r : S) ≤ (r : S) + 1 := by
        simpa using H.add_mono (le_rfl (a := (r : S))) (H.zero_le 1)
      simpa [mul_comm] using H.mul_mono (y ^ m) hsucc

end Spectral

end VPVNP
end Computability
end OAI
