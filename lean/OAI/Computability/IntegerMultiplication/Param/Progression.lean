import OAI.Computability.IntegerMultiplication.Param.Spacing

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Param

-- generate sizes inside full gap
def red (d J : ℕ) := 2*Nat.factorial d*J
def lift_ (d t D : ℕ) := (8*d-2)*t/(8*d*D)+1
def stage (d t D i : ℕ) := (lift_ d t D+i)*D+1
theorem stage_margin {d t D i} (a : 1≤d) (b : 1≤D) (c : i<d)
    (h : 128*d^2*D≤t) :
    Margin d t (stage d t D i) := by
  let B := 8*d
  let C := B*D
  let F := (B-2)*t
  have b₁ : 2 ≤ B := by dsimp [B]; omega
  have c₁ : 0<C := by unfold C; exact Nat.mul_pos (by omega) b
  have u : F/C*C≤F := Nat.div_mul_le_self _ _
  have v : F<C*lift_ d t D := by
    unfold lift_
    change F < C*(F/C+1)
    rw [mul_comm C]; apply (Nat.div_lt_iff_lt_mul c₁).mp; omega
  refine ⟨le_trans (Nat.le_of_lt v) ?_,?_⟩
  · unfold stage C B
    rw [show 8*d*(_*D+1) = (8*d*D)*lift_ d t D +(8*d*D)*i+8*d by ring]
    omega
  have q : (B-2)+1=B-1 := by omega
  change B*stage d t D i ≤ _
  change _ ≤ (B-1)*t
  rw [← q,Nat.add_mul,one_mul]
  unfold stage lift_
  change B*((F/C+1+i)*D+1)≤ F+t
  have e : C*(1+i)+B≤t := by
    refine le_trans ?_ h
    unfold C B
    have t := Nat.mul_le_mul_left (8*d*D) (by omega : 1+i ≤ d)
    have n : 8*d ≤ 8*d*D*d := le_trans (by nlinarith [Nat.mul_le_mul_left (8*d) b] : 8*d ≤ 8*d*D) (by
      exact Nat.le_mul_of_pos_right _ a)
    nlinarith [Nat.zero_le (d^2*D)]
  rw [show B*((F/C+1+i)*D+1)=F/C*C+(C*(1+i)+B) by unfold C; ring]
  exact Nat.add_le_add u e

theorem stage_odd {d t J i} : Odd (stage d t (red d J) i) := by
  let v := lift_ d t (red d J)
  refine ⟨Nat.factorial d*J*(v+i),?_⟩
  unfold stage red
  unfold v red
  ring

theorem relatively {d t J i} {p : ℕ} (P : Nat.Prime p)
    (q : p∣stage d t (red d J) i) :
    ¬ p ∣ red d J := by
  intro a
  have w : p∣ (lift_ d t (red d J)+i)*red d J :=
    Nat.dvd_trans a (Nat.dvd_mul_left ..)
  have e : p∣ 1 := (Nat.dvd_add_iff_right w).mpr q
  have h := Nat.le_of_dvd (by decide : 0<1) e
  have u := P.two_le
  omega
theorem rel_square {d t J i} :
    Nat.Coprime (stage d t (red d J) i) (J^2) :=
  Nat.coprime_of_dvd fun _p P q z=> relatively P q ((P.dvd_of_dvd_pow z).trans
    (Nat.dvd_mul_left ..))
theorem disjoint_lt {d t J i l : ℕ} (h : l < i) (e : i < d) :
    Nat.Coprime (stage d t (red d J) i) (stage d t (red d J) l) := by
  let D := red d J
  refine Nat.coprime_of_dvd fun p P q z=> ?_
  have w : p∣ (i-l)*D := (Nat.dvd_add_iff_right z).mpr ((show stage d t D l+(i-l)*D=stage d t D i from by
    unfold stage
    rw [Nat.add_mul,Nat.add_mul,add_right_comm (b:=1), add_assoc (lift_ d t D *D),← Nat.add_mul l, Nat.add_sub_cancel' h.le]) ▸ q)
  obtain w|w := P.dvd_mul.mp w
  · exact relatively P q (Nat.dvd_trans w (Nat.dvd_trans
      (Nat.dvd_factorial (by omega) (by omega : i-l≤d)) (show Nat.factorial d ∣ D by
        exact dvd_mul_of_dvd_left (Nat.dvd_mul_left ..) _)))
  exact relatively P q w

theorem disjoint_ {d t J i l : ℕ} (h : i≠l) (h₀ : i < d) (h₁ : l < d) :
    Nat.Coprime (stage d t (red d J) i) (stage d t (red d J) l) := by
  rcases lt_or_gt_of_ne h with v | v
  · exact (disjoint_lt v h₁).symm
  exact disjoint_lt v h₀
end Param

end IntegerMultiplication
end Computability
end OAI
