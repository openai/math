import OAI.Computability.MultitapeWeakETH.MotifProgram

/-! # Computing the fixed motif's admission data from unary demand widths -/

namespace OAI.Computability.MultitapeWeakETH.MotifFields

open IntegerMultiplication Code VPVNP StackInterpreter Carry Strip Staff
open scoped Classical
noncomputable section

variable {D : Type} [Fintype D] (p : D → ℚ)
abbrev Widths := List Tally
private abbrev reg : Regime Widths := ⟨size,send,Dom.base _⟩

def raw (xs : Widths) (i : D) := (fetch [] i xs).length

private theorem width_nat (i : D) : Realizes reg (fun xs => raw xs i) := by
  change Poly (fun xs : Widths => tally (fetch [] i xs).length)
  simpa only [recover_tally] using fetch_poly ([] : Tally) i

theorem energy_nat : Realizes reg (fun xs => MotifAdmission.energy p (raw xs)) := by
  have sum (s : Finset D) : Realizes reg (fun xs => ∑ i ∈ s, MotifAdmission.weight p i * (raw xs i)^2) := by
    induction s using Finset.induction_on with
    | empty => simpa using (Realizes.fix (r:=reg) 0)
    | insert i s hi ih =>
      have e := (Realizes.fix (r:=reg) (MotifAdmission.weight p i)).times ((width_nat i).times (width_nat i))
      simpa only [Finset.sum_insert hi,pow_two] using e.plus ih
  exact sum Finset.univ

theorem copies_poly (L : ℕ) : Poly (fun xs : Widths => tally (MotifAdmission.copies p (raw xs) L)) := by
  let e (xs : Widths) := MotifAdmission.energy p (raw xs)
  let d := L^2*MotifAdmission.denominator p
  have en : Realizes reg e := energy_nat p
  have quotient := (en.minused (Realizes.fix 1)).dividing (Realizes.fix d)
  have root : Realizes reg (fun xs => ((e xs-1)/d).sqrt) :=
    (Figure.of_spoken quotient).rooted.pay ((diameter _ quotient).mono fun _ => Nat.sqrt_le_self _)
  have pos : Poly (fun xs : Widths => decide (0<e xs)) := by
    simpa only [Iter.small,List.length_nil,tally_length] using ((Code.Poly.const ([] : Tally)).pair (show Poly (fun xs => tally (e xs)) from en)).compose Iter.small_easy.poly
  have result := Poly.choose pos (show Poly (fun xs : Widths => tally (((e xs-1)/d).sqrt+1)) from root.plus (Realizes.fix 1))
    (Code.Poly.const (tally 0))
  convert result using 1
  funext xs
  change tally (MotifAdmission.ceilRoot (e xs) d) = _
  by_cases h : e xs=0 <;> simp [MotifAdmission.ceilRoot,MotifAdmission.floorRoot_eq,h,Nat.pos_of_ne_zero]

private theorem covers_poly (z : D → ℚ) :
    Poly (fun xs : Widths => decide (∀ i, MotifAdmission.coversCoordinate p (raw xs) i (z i) = true)) := by
  apply all_poly
  intro i
  by_cases h : 0≤z i
  · let u := (width_nat i).times (Realizes.fix (z i).den)
    have left := (u.times u).times (Realizes.fix (MotifAdmission.denominator p))
    have right := (energy_nat p).times (Realizes.fix ((z i).num.natAbs^2))
    have lt := ((show Poly (fun xs => tally (MotifAdmission.energy p (raw xs)*(z i).num.natAbs^2)) from right).pair
      (show Poly (fun xs => tally ((raw xs i*(z i).den)*(raw xs i*(z i).den)*MotifAdmission.denominator p)) from left)).compose Iter.small_easy.poly
    convert lt.compose Iter.negate.poly using 1
    funext xs
    apply Bool.eq_iff_iff.mpr
    simp [MotifAdmission.coversCoordinate,h,Iter.small,pow_two]
  · simpa [MotifAdmission.coversCoordinate,h] using (Code.Poly.const (X:=Widths) false)

end
end OAI.Computability.MultitapeWeakETH.MotifFields
