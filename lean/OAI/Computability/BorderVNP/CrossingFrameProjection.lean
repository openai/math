import OAI.Computability.BorderVNP.CrossingFrameCNF
import OAI.Computability.BorderVNP.CrossingSplitQuery

/-! # Specializing the universal signed family to a weighted Boolean frame

The frame arities and number of gates bound its literal CNF linearly. The literal
query compiler then gives one fixed polynomial length bound, and padding supplies
the projection at every greater length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open VPVNP HardnessCNF MvPolynomial VerifierNetwork
open scoped Classical

private theorem weightedLength_le (B k L : ℕ) (hk : k ≤ 2 + 6*B) (hL : L ≤ 3 + 32*B) :
    1000 * ((L+1)*(2+L)*(k+1)+1)^2+k ≤ 100000000000 * (B+1)^6 := by
  let b := B + 1
  have h1 : L+1 ≤ 33*b := by dsimp [b]; omega
  have h2 : 2+L ≤ 34*b := by dsimp [b]; omega
  have h3 : k+1 ≤ 7*b := by dsimp [b]; omega
  have hp : 1 ≤ b^3 := Nat.pow_pos (by dsimp [b]; omega)
  have hk6 : k ≤ 6 * b^6 := by
    have h := Nat.pow_le_pow_right (show 0 < b by dsimp [b]; omega) (show 1 ≤ 6 by decide)
    simp only [pow_one] at h
    dsimp [b] at *
    omega
  calc
    _ ≤ 1000 * ((33*b)*(34*b)*(7*b) + b^3)^2 + 6*b^6 := by gcongr
    _ ≤ 100000000000 * b^6 := by ring_nf; omega

/-- All sufficiently long signed polynomials project to the weighted Boolean-sum
of the frame, with a degree-six uniform length bound in its dimensions and gate count. -/
theorem frame_projection_at_length {R V σ O τ : Type*} [CommRing R] [Fintype σ]
    [Fintype O] [Fintype τ] (f : Frame σ O) (accept : O) (outputs : τ → O)
    (w : Projection R τ V) (B n : ℕ) (hσ : Fintype.card σ ≤ B) (hτ : Fintype.card τ ≤ B)
    (hf : f.size ≤ B) (hn : 100000000000 * (B+1)^6 ≤ n) :
    ∃ φ : Projection R (Fin n × Bool) V,
      φ.hom (MvPolynomial.map (Int.castRingHom R) (Pstar n)) =
        ∑ x : σ → Bool, if f.eval x accept then
          ∏ j, if f.eval x (outputs j) then (w j).elim X C else 1 else 0 := by
  obtain ⟨k, hk, c, hc, a, ha⟩ := FrameCNF.exists_weightedCNF f accept outputs w
  have h := weightedLength_le B k (literalCount c) (by omega) (by omega)
  obtain ⟨φ, hφ⟩ := weightedCNF_projection_at_length c a n (h.trans hn)
  exact ⟨φ, hφ.trans ha⟩

end Crossing

end BorderVNP
end Computability
end OAI
