import OAI.ThreeFlat.Diagonal.TraceBucketGeometry

namespace OAI
/-! # Native arithmetic inverses of the tag and cell enumerations -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout

variable {F : Type*} {p k low o c : ℕ} {N : BitNetwork F p}

private theorem peel {b j : ℕ} (a : ℕ) (hj : j<b) :
    (a*b+j)/b=a ∧ (a*b+j)%b=j := by
  have pos : 0<b := by omega
  constructor
  · rw [Nat.add_comm,Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt hj,Nat.zero_add]
  · rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hj]

theorem tag_digits (t : Fin o × PayloadAddress low c) :
    let j := ((tagOrder o low c).symm t).val
    j/(2^low*(c*3))=t.1.val ∧ (j/(c*3))%2^low=t.2.1.val ∧
      (j/3)%c=t.2.2.1.val ∧ j%3=t.2.2.2.val := by
  intro j
  let q := t.1.val*2^low+t.2.1.val
  let g := q*c+t.2.2.1.val
  have x := peel g t.2.2.2.isLt
  have y := peel q t.2.2.1.isLt
  have z := peel t.1.val t.2.1.isLt
  have raw : j=g*3+t.2.2.2.val := tagNumber t
  have l : j/3=g := raw ▸ x.1
  have m : j/(c*3)=q := by
    rw [Nat.mul_comm c 3,← Nat.div_div_eq_div_mul,l]
    exact y.1
  refine ⟨?_,m ▸ z.2,l ▸ y.2,raw ▸ x.2⟩
  rw [Nat.mul_comm (2^low) (c*3),← Nat.div_div_eq_div_mul,m]
  exact z.1

theorem joinedRow (lane : Lane k) (lo : Fin (2^low)) :
    ((splitRow k low).symm (lane,lo)).val=(finFunctionFinEquiv lane).val*2^low+lo.val := by
  change lo.val+2^low*(finFunctionFinEquiv lane).val=_
  ac_rfl

theorem laneCell_digits (P : RowLayout N (k+1) low o c) (R : P.Rectangular) (lane : Lane (k+1))
    (i : Fin (2^low*c)) :
    (P.cellAddress (P.laneCellOrd R lane i).val).1.val =
      (finFunctionFinEquiv lane).val*2^low+i.val/c ∧
    (P.cellAddress (P.laneCellOrd R lane i).val).2.val=i.val%c := by
  have chart : P.cellAddress (P.laneCellOrd R lane i).val =
      ((splitRow _ _).symm (lane,(finProdFinEquiv.symm i).1),(finProdFinEquiv.symm i).2) :=
    R.at_cell _ _
  rw [chart,joinedRow]
  exact ⟨rfl,rfl⟩

end ThreeFlat.Diagonal.LaneCursor.RowLayout

end OAI
