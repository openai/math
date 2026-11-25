import OAI.Computability.BorderVNP.ParseBatchVerifierTreesCost

/-!
# Word and lane bounds for the two child reads per production

Each tree uses one table row and two request lanes per record. Rounding this
array to a power of two leaves its capacity linear in the degree.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchTrees

open BorderVNP.ParseRecords

/-- Arithmetic work per raw row, the batch sort of requests, and final flag tests. -/
def childWork (J a b : ℕ) : ℕ :=
  J*(a+1)^3 + 2^b*(b+1)^2*(a+1) + (J+1)

/-- The power-of-two padding and widened address words give a linear-in-degree,
cubic-logarithmic bound for the structure verifier. -/
theorem childWork_le {m g n r : ℕ} (d : Fin n) (hm : m = d.val+1)
    (hr : 0 < r) (hw : max m (max g n)+1 ≤ 2*m*r) :
    let J := 2*d.val+1
    childWork J (recordWidth m g n+3) (Nat.clog 2 (3*J)) ≤
      100*m*(Nat.clog 2 (2*m*r)+3)^3 := by
  let J := 2*d.val+1
  let L := Nat.clog 2 (2*m*r)
  let b := Nat.clog 2 (3*J)
  let a := recordWidth m g n+3
  have hJ : J ≤ 2*m := by dsimp [J]; omega
  have hJpos : 0 < J := Nat.succ_pos _
  have hcap : 2^b ≤ 12*m :=
    (TeamSorting.padding_lt_twice (Nat.mul_pos (by decide : 0 < 3) hJpos)).le.trans (by omega)
  have hmr : 2*m ≤ 2*m*r := Nat.le_mul_of_pos_right _ hr
  have hblog : b ≤ L+2 := by
    apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
    rw [pow_add]
    have hL : 2*m*r ≤ 2^L := Nat.le_pow_clog (by decide) _
    omega
  have halog : a+1 ≤ 2*(L+3) := by
    have hh : recordWidth m g n ≤ L := Nat.clog_mono_right 2 hw
    dsimp only [a]; omega
  change J*(a+1)^3 + 2^b*(b+1)^2*(a+1) + (J+1) ≤ 100*m*(L+3)^3
  calc
    _ ≤ (2*m)*(2*(L+3))^3 + (12*m)*(L+3)^2*(2*(L+3)) + (2*m+1) := by
      have hb₁ : b+1 ≤ L+3 := by omega
      exact Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul hJ (Nat.pow_le_pow_left halog 3))
        (Nat.mul_le_mul (Nat.mul_le_mul hcap (Nat.pow_le_pow_left hb₁ 2)) halog))
        (Nat.add_le_add_right hJ 1)
    _ ≤ 100*m*(L+3)^3 := by ring_nf; omega

/-- The two row frames, input preparation, sorting phases and adjacency scan fit
a common constant times the three terms of the child-verifier work bound. -/
theorem child_layout_le (J a b : ℕ) :
    let p := a+a
    2*(J*(2+6*a)*(300*(a+1)^2)) + (2*J+1) + 2^b*((p+1)+a)*8 +
      b^2*(2^b*(24*((p+1)+a)+1)) + 2^b*(10*(a+p)+11) + 5 ≤ 10000 * childWork J a b := by
  dsimp [childWork]
  ring_nf
  omega

end ParseBatchTrees

end BorderVNP
end Computability
end OAI
