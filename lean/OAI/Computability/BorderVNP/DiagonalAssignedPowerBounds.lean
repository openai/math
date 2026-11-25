import OAI.Computability.BorderVNP.DiagonalChosenReader
import OAI.Computability.BorderVNP.TeamSorting

/-! # Box and binary word bounds for the actual assigned parameter powers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch ResidueBox ResidueIndex
open scoped BigOperators Classical

variable {Gadget : Type*} {teams h k r : ℕ}

/-- The real weighted use bits give the degree bound of the residue chart
for every assigned term, including unrestricted and repeated occurrences. -/
theorem Tally.assigned_degree (t : Tally (Fin teams) (Fin h) Gadget (Nat.clog 2 (r*(2*k+1)+1))) :
    t.exponents.degree ≤ batchDegree teams h r k := by
  simpa only [Tally.exponents,batchDegree,Fintype.card_fin] using exponent_degree_le t.powers

/-- The true parameter shift lies in the chart box on all coordinates. -/
theorem Tally.assigned_shift (t : Tally (Fin teams) (Fin h) Gadget (Nat.clog 2 (r*(2*k+1)+1))) (deg : ℕ) :
    Fits (radius (batchDegree teams h r k) deg) (parameterShift t.exponents) := by
  intro i
  have hl := t.assigned_degree
  cases i with
  | none =>
    change -(radius (batchDegree teams h r k) deg : ℤ) ≤ 0 ∧ 0 ≤ _
    omega
  | some i =>
    have hμ := (Finsupp.le_degree i t.exponents).trans hl
    change -(radius (batchDegree teams h r k) deg : ℤ) ≤ (t.exponents i : ℤ) ∧
      (t.exponents i : ℤ) ≤ radius (batchDegree teams h r k) deg
    unfold radius
    omega

/-- At the source schedule, the full degree, even when all grammar slots
are selected, is bounded by a fixed polynomial in the batch input length. -/
theorem assigned_degree_polynomial (teams r k s : ℕ) (hr : 1 ≤ r)
    (ht : teams ≤ r*(k+1)+1) (hs : s ≤ r*(k+1)+1) :
    batchDegree teams (pairedTableParameters (k+1) s) r k ≤ 288*(r*(k+1)+1)^7 := by
  let M := r*(k+1)+1
  have hM : 0 < M := Nat.succ_pos _
  have hn : k+1 ≤ M := (Nat.le_mul_of_pos_left _ hr).trans (Nat.le_succ _)
  have hsum : 2*(k+1)+s+1 ≤ 4*M := by change s ≤ M at hs; omega
  have h2 : M^2 ≤ M^5 := Nat.pow_le_pow_right hM (by decide)
  have hh : pairedTableParameters (k+1) s ≤ 72*M^5 := by
    calc
      _ ≤ (2*(k+1)+s+1)*(2*(k+1)) + (k+1)^2*(2*(k+1)+s+1)^3 :=
        pairedTableParameters_le _ _
      _ ≤ (4*M)*(2*M) + M^2*(4*M)^3 :=
        Nat.add_le_add (Nat.mul_le_mul hsum (Nat.mul_le_mul_left 2 hn))
          (Nat.mul_le_mul (Nat.pow_le_pow_left hn _) (Nat.pow_le_pow_left hsum _))
      _ = 8*M^2+64*M^5 := by ring
      _ ≤ _ := by omega
  have hinput : r*(2*k+1)+1 ≤ 2*M := by
    dsimp [M]
    nlinarith
  have hw : 2^Nat.clog 2 (r*(2*k+1)+1)-1 ≤ 4*M := by
    have hp : 2^Nat.clog 2 (r*(2*k+1)+1) < 2*(r*(2*k+1)+1) :=
      TeamSorting.padding_lt_twice (Nat.succ_pos _)
    omega
  calc
    _ ≤ (M*(72*M^5))*(4*M) := Nat.mul_le_mul (Nat.mul_le_mul ht hh) hw
    _ = _ := by ring

/-- Each numbered parameter word in the live residue call therefore fits
the same physical word capacity used by the genuine RAM and tally header. -/
theorem Tally.assigned_power_lt {s tally : ℕ}
    (t : Tally (Fin teams) (Fin (pairedTableParameters (k+1) s)) Gadget (Nat.clog 2 (r*(2*k+1)+1)))
    (hr : 1 ≤ r) (ht : teams ≤ r*(k+1)+1) (hs : s ≤ r*(k+1)+1)
    (room : 288*(r*(k+1)+1)^7 < 2^tally) (i : Fin (pairedTableParameters (k+1) s)) :
    t.exponents i < 2^tally :=
  (Finsupp.le_degree i t.exponents).trans_lt
    (t.assigned_degree.trans_lt ((assigned_degree_polynomial teams r k s hr ht hs).trans_lt room))

end Diagonal

end BorderVNP
end Computability
end OAI
