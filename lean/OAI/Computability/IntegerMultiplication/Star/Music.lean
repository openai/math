import OAI.Computability.IntegerMultiplication.Brief.Curve
import OAI.Computability.IntegerMultiplication.Star.Disk

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Star
open Code Brief Carry Staff Strip
variable {J : Type} {r:Regime J}
theorem natB (k:ℕ) : Blot r (fun _=>(k:ℝ)) := Blot.natural (.natural k)
private theorem plusOne :
    Blot r (fun _=>(1:ℝ)) := by simpa using (natB (r:=r) 1)
private theorem minusOne :
    Blot r (fun _=> (-1:ℝ)) := plusOne.minus

theorem arc_master (x:J→ℝ) (h:Blot r x) (n:J→ℕ)
    (t:Realizes r n) :
    Blot r (fun i=>arc (x i) (n i)) := by
  let s:=signal n t
  let p:= Sigma.fst (β:=fun i=>Fin (n i))
  let j (i:Across n) := i.2.val
  have z: Realizes s j := floor_ n t
  let k (i:Across n) := 2*j i+1
  have q : Realizes s k := (Realizes.times (.fix 2) z).plus (.fix 1)
  have P := (h.extend n t).power q
  apply Blot.sums n t
  exact ((minusOne.power z).times P).ratio (Blot.natural (Figure.of_spoken q)) (fun i=> by positivity)

theorem atlas (n:J→ℕ) (t:Realizes r n) :
    Blot r (fun i=>polestar (n i)) := by
  have P := arc_master (fun i:J=> (2:ℝ)⁻¹) (((by norm_num; exact (natB (r:=r) 2) : Blot r (fun _=> ((2:ℕ):ℝ))).invpos
    (fun i=>by norm_num))) n t
  have Q := arc_master _ ((natB (r:=r) 3).invpos (by norm_num)) n t
  have H := (natB (r:=r) 4).times (P.adding Q)
  norm_num1 at *
  simpa only [polestar, one_div] using H

variable (x:J→ℝ) (h:Blot r x) (n:J→ℕ) (v:Realizes r n)
include h v
open Complex

theorem motor_rule :
    Curve r (fun i=> emotor (x i) (n i)) := by
  let s:=signal n v
  let j (i:Across n) := i.2.val
  have z: Realizes s j := floor_ n v
  let l (i:Across n) := x i.1 ^ j i
  have t : Blot s l := (h.extend n v).power z
  have T := t.ratio (Blot.natural (Figure.fact z)) (fun i=>by
    exact_mod_cast (Nat.factorial_pos (j i)))
  have q := (Curve.real T).mul (Curve.oddity z)
  apply Curve.sums
  have eq (t:ℝ) (n:ℕ) : ((↑t:ℂ)*I)^n/Nat.factorial n=
      (↑(t^n/Nat.factorial n:ℝ):ℂ)*I^n := by rw [mul_pow]; push_cast; ring
  simp_rw [eq]
  exact q
theorem critical :
    Curve r (fun i=> needle (n i) (x i)) := by
  have p := ((atlas n v).times h).ratio (natB 16) (by norm_num)
  norm_num1 at p
  exact (motor_rule (fun i=>inclination (n i) (x i)) p n v).fixedPower 32
theorem sailRule (d:J→ℕ) (c:Realizes r d) :
    Blot r (fun i=>sail (n i) (d i) (x i)) := by
  have P := h.ratio (natB 2) (by norm_num)
  norm_num1 at P
  have w := critical (fun i=> x i/2) P n v
  exact (minusOne.maximum (w.1.minimum plusOne)).power (Realizes.times (.fix 2) c)

end Star

end IntegerMultiplication
end Computability
end OAI
