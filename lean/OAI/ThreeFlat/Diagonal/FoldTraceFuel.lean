import OAI.ThreeFlat.Diagonal.HProgramBudget

namespace OAI
/-! # Numerical charges for the native H evaluator's input preparation -/

namespace ThreeFlat.Diagonal.FoldTrace

/-- Time allowance for one native fold entry. -/
def entryFuel (u A L : ℕ) := 2^(u^3)*2^(u^10)*L/u^A

/-- The startup bound with one extra power of u leaves at least half of the true
entry budget for the continuation at exactly the same geometric register width. -/
theorem startup_half {u A L : ℕ} (hu : 2≤u) : entryFuel u (A+1) L≤entryFuel u A L/2 := by
  have splitFuel : entryFuel u (A+1) L=entryFuel u A L/u := by
    unfold entryFuel
    rw [pow_succ u A,Nat.div_div_eq_div_mul]
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
  calc
    _ ≤ entryFuel u (A+1) L*u := Nat.mul_le_mul_left _ hu
    _ = (entryFuel u A L/u)*u := by rw [splitFuel]
    _ ≤ _ := Nat.div_mul_le_self ..

theorem volume_le_entryFuel {u A L : ℕ} (hu : 1≤u) (ha : A≤u) (hl : 1≤L) :
    2^(u^10)≤entryFuel u A L := by
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos hu)).mpr
  have q := (width_pow_le_two_pow_sq ha).trans
    (Nat.pow_le_pow_right (by decide : 0<2) (Nat.pow_le_pow_right hu (by decide : 2≤3)))
  calc
    _ ≤ 2^(u^10)*2^(u^3) := Nat.mul_le_mul_left _ q
    _ = 2^(u^3)*2^(u^10) := Nat.mul_comm ..
    _ ≤ _ := Nat.le_mul_of_pos_right _ hl

/-- The preliminary H program scans the old local table, writes the new X
rows once, and initializes the genuine contraction's hidden variables. -/
theorem prelude_charge {u cap t n B a q par packedSize products X Y pre : ℕ}
    (hu : 200000≤u) (hp : 1≤cap) (hB : B≤cap) (ha : a≤cap) (hNa : n*a≤cap)
    (hq : q≤cap) (hpar : par≤cap) (hm : packedSize≤2*cap) (hprod : products≤2*cap)
    (trace : X+Y≤cap*u^142)
    (charge : pre≤2122+12000*(1+(2*(B+B)+q)+par+packedSize+Y+
      ((2+(q+(((B+B)+a)+((B+B)+a))))+
       (t*((B+B)+a)+(t+1)*(n*a)+(t+1)*X))+products)) :
    pre≤128*((t+1)*(cap*u^144)) := by
  let per := cap*u^142
  let all := (t+1)*per
  have cp : cap≤per := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  have pa : per≤all := Nat.le_mul_of_pos_left _ (by omega)
  have ca := cp.trans pa
  have mul (x : ℕ) (h : x≤per) : (t+1)*x≤all := Nat.mul_le_mul_left _ h
  have first : t*((B+B)+a)≤3*all := calc
    _ ≤ (t+1)*(3*per) := Nat.mul_le_mul (by omega) (by omega)
    _ = 3*all := by dsimp [all]; ring
  have mid := mul _ (hNa.trans cp)
  have cell := mul X (by change X≤cap*u^142; omega)
  have y : Y≤all := (by omega : Y≤per).trans pa
  have pos : 1≤all := hp.trans ca
  have cost : pre≤500000*all := by omega
  have coeff : 500000≤128*u^2 := by
    have hu2 := Nat.le_self_pow (by decide : 2≠0) u
    omega
  calc
    _ ≤ 500000*all := cost
    _ ≤ (128*u^2)*all := Nat.mul_le_mul_right _ coeff
    _ = _ := by dsimp [all,per]; ring

theorem field_charge {u cardinal cap : ℕ} (pos : 1≤u) (fit : cardinal≤u) (room : u^4≤cap) :
    (cardinal*cardinal)*(cardinal*cardinal+1)≤2*cap := by
  have square : cardinal*cardinal≤u^2 := by simpa only [sq] using Nat.mul_le_mul fit fit
  have fourth : (cardinal*cardinal)*(cardinal*cardinal)≤u^4 := calc
    _ ≤ u^2*u^2 := Nat.mul_le_mul square square
    _ = u^4 := by ring
  have small := square.trans ((Nat.pow_le_pow_right pos (by decide : 2≤4)).trans room)
  rw [Nat.mul_succ]
  omega

end ThreeFlat.Diagonal.FoldTrace

end OAI
