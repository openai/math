import OAI.Computability.BorderVNP.PackedHistorySubdivisionBatch

/-! # Sparse public cost of a whole physical epoch input boundary -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.RouteRows

open Shortening.PublicCapacity Cover.AddressCircuit StackFrame

/-- The complete gate bound for all geodesic subdivisions is linear in the number
of reserved site and cable rows, with polynomial dependence on level and public
word length. Both the catalog and subdivision length are fixed before the inputs. -/
theorem subdivision_work_le (q extra A a copies : ℕ) :
    ∃ C e : ℕ, ∀ (d w : ℕ) (s : Shape),
      1+copies*(300*(s.sites+2*s.edges+1)*
        (Nat.clog 2 (s.sites+2*s.edges)+w+Fintype.card (ProductSlots q (d+1))+1)^3 +
        1+(s.subdivide extra).sites*A*(d+2)^a+(s.subdivide extra).edges*(2+3*w)*8) ≤
      C*(s.sites+s.edges+1)*(d+w+Nat.clog 2 (s.sites+2*s.edges+1)+3)^e := by
  let coeff := 600*(3+90*q)^3 + 1 + (2*extra+1)*A + (2*extra+1)*5*8
  let e := max 3 a
  refine ⟨1+copies*coeff,e,?_⟩
  intro d w s
  let N := s.sites+s.edges+1
  let W := d+w+Nat.clog 2 (s.sites+2*s.edges+1)+3
  have hW : 1≤W := by dsimp [W]; omega
  have hd : d+2 ≤ W := by dsimp [W]; omega
  have hw : w ≤ W := by dsimp [W]; omega
  have hcl : Nat.clog 2 (s.sites+2*s.edges) ≤ W :=
    (Nat.clog_mono_right 2 (Nat.le_succ _)).trans (by dsimp [W]; omega)
  have hfield : Fintype.card (ProductSlots q (d+1)) = 90*q*(d+2) := by simp [ProductSlots,Slots,width]; ring
  have hwires : Nat.clog 2 (s.sites+2*s.edges)+w+Fintype.card (ProductSlots q (d+1))+1 ≤ (3+90*q)*W := by
    rw [hfield,Nat.add_mul]
    have h := Nat.mul_le_mul_left (90*q) hd
    omega
  have vol := s.subdivide_volume extra 0
  have hvol : (s.subdivide extra).sites+(s.subdivide extra).edges+1 ≤ (2*extra+1)*N := by
    simpa only [Shape.volume,N,Nat.add_zero] using vol
  have hn : 1 ≤ N := by dsimp [N]; omega
  have hsites : (s.subdivide extra).sites ≤ (2*extra+1)*N := by omega
  have hedges : (s.subdivide extra).edges ≤ (2*extra+1)*N := by omega
  have haddr : s.sites+2*s.edges+1 ≤ 2*N := by dsimp [N]; omega
  have hpow : W^3 ≤ W^e := Nat.pow_le_pow_right hW (le_max_left ..)
  have hpowa : (d+2)^a ≤ W^e := (Nat.pow_le_pow_left hd a).trans (Nat.pow_le_pow_right hW (le_max_right ..))
  have hlinear : W ≤ W^e := (Nat.le_self_pow (by dsimp [e]; omega) W)
  have hcost : 2+3*w ≤ 5*W^e := by omega
  have hrow : 1 ≤ N*W^e := Nat.mul_pos hn (Nat.pow_pos hW)
  have hjoin : 300*(s.sites+2*s.edges+1)*(Nat.clog 2 (s.sites+2*s.edges)+w+Fintype.card (ProductSlots q (d+1))+1)^3 ≤
      600*(3+90*q)^3*N*W^e := by
    calc
      _ ≤ 300*(2*N)*(((3+90*q)*W)^3) := Nat.mul_le_mul (Nat.mul_le_mul_left _ haddr) (Nat.pow_le_pow_left hwires 3)
      _ = 600*(3+90*q)^3*N*W^3 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hpow
  have hsites' := Nat.mul_le_mul (Nat.mul_le_mul_right A hsites) hpowa
  have hedges' := Nat.mul_le_mul_right 8 (Nat.mul_le_mul hedges hcost)
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hjoin hrow) hsites') hedges'
  calc
    _ ≤ N*W^e+copies*(600*(3+90*q)^3*N*W^e + N*W^e + ((2*extra+1)*N)*A*W^e + ((2*extra+1)*N)*(5*W^e)*8) :=
      Nat.add_le_add hrow (Nat.mul_le_mul_left copies hsum)
    _ = _ := by change _ = (1+copies*coeff)*N*W^e; dsimp [coeff]; ring

end PackedHistoryCircuit.RouteRows

end BorderVNP
end Computability
end OAI
