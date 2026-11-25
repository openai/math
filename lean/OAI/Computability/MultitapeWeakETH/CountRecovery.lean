import OAI.Computability.MultitapeWeakETH.IntegralResidues
import OAI.Computability.IntegerMultiplication.Carry.Figure

/-! # Reading the exact sparse model count from the bounded integral accumulator -/

namespace OAI.Computability.MultitapeWeakETH.TemplateArithmetic

open IntegerMultiplication Code Bits Grid Staff Strip Carry
open private wordAt wordAt_poly wordAt_ofFn from OAI.Computability.MultitapeWeakETH.IntegralInstructions
open scoped Classical
noncomputable section

/-- The unsigned distance to the nearest multiple of the modulus recovers
the magnitude of a small signed integer from either signed representative. -/
private theorem magnitude {m : ℕ} {x y : ℤ} (raw : x.natAbs < m) (small : 2*y.natAbs < m)
    (div : (m:ℤ) ∣ y-x) : min x.natAbs (m-x.natAbs) = y.natAbs := by
  obtain ⟨z,hz⟩ := div
  have pos : (0:ℤ) < m := by exact_mod_cast (by omega : 0 < m)
  have rx : -(m:ℤ) < x ∧ x < (m:ℤ) := by omega
  have ry : -(m:ℤ) < y ∧ y < (m:ℤ) := by omega
  have lo : -1 ≤ z := by
    by_contra! bad
    have h := mul_le_mul_of_nonneg_left (show z ≤ -2 by omega) pos.le
    linarith
  have hi : z ≤ 1 := by
    by_contra! bad
    have h := mul_le_mul_of_nonneg_left (show 2 ≤ z by omega) pos.le
    linarith
  interval_cases z <;> simp at hz <;> omega

/-- The three inputs are the denominator exponent, the binary modulus width
and the list of signed coordinates. The returned word is an unsigned count. -/
private abbrev Request := Tally × Tally × List S
private abbrev regime : Regime Request := ⟨size,send,Dom.base _⟩

private theorem recoverProgram (i : ℕ) (d a : ℤ) :
    Figure regime (fun q => let x := (whole (wordAt i q.2.2)).natAbs
      min x (2^q.2.1.length-x) / (d.natAbs^q.1.length*a.natAbs)) := by
  have exp : Realizes regime (fun q => q.1.length) := by
    change Poly (fun q : Request => tally q.1.length)
    simpa only [recover_tally] using (Easy.fst (X:=Tally) (Y:=Tally × List S)).poly
  have w : Realizes regime (fun q => q.2.1.length) := by
    change Poly (fun q : Request => tally q.2.1.length)
    simpa only [recover_tally] using (Easy.snd (X:=Tally) |>.compose (Easy.fst (Y:=List S))).poly
  have mag : Figure regime (fun q => (whole (wordAt i q.2.2)).natAbs) := by
    refine ⟨_,((Easy.snd.compose Easy.snd).poly.compose (wordAt_poly i)).sndCompose,fun q => (normal _).symm⟩
  let delta := ((Figure.natural 2).repeated w).subtracted mag
  have lower := mag.variant delta (mag.compare_ delta)
  simpa only [min_def_lt] using lower.quotients (((Figure.natural d.natAbs).repeated exp).multiplied (Figure.natural a.natAbs))

/-- A single polynomial-time signed-word decoder converts the residue of
d^M times a count into the full unsigned count for the DFS addition. -/
theorem recover_count_program {R : Type} [CommRing R] [Nontrivial R] [CharZero R] {m : ℕ}
    (basis : Module.Basis (Fin m) ℤ R) (d : ℤ) (hd : d ≠ 0) :
    ∃ (A : ℕ) (read : Tally × Tally × List S → Word), Poly read ∧
      ∀ (n M c : ℕ) (ws : List S), c ≤ 2^n →
        let w := A*(M+1)+n+2
        FitsWidth m w ws → (2:R)^w ∣ ((d^M*(c:ℤ) : ℤ) : R) - decodeCoordinates basis ws →
        value (read (tally M,tally w,ws)) = c := by
  have existsCoord : ∃ i, basis.repr 1 i ≠ 0 := by
    by_contra! hz
    exact one_ne_zero (basis.repr.map_eq_zero_iff.mp (Finsupp.ext fun i => hz i))
  obtain ⟨i,hi⟩ := existsCoord
  let a := basis.repr 1 i
  let A := a.natAbs+d.natAbs+1
  obtain ⟨read,poly,eval⟩ := recoverProgram i.val d a
  refine ⟨A,read,poly,?_⟩
  intro n M c ws small w bounds congr
  let x := whole (wordAt i.val ws)
  let y := d^M*(c:ℤ)*a
  have words : ∃ f : Fin m → S, ws = List.ofFn f := by
    let f (j : Fin m) := ws[j.val]'(bounds.1 ▸ j.isLt)
    exact ⟨f,List.ext_getElem (by simp [bounds.1]) (by simp [f])⟩
  obtain ⟨f,rfl⟩ := words
  have xi : x = whole (f i) := by simp [x,wordAt_ofFn]
  have raw : x.natAbs < 2^w := by
    rw [xi,normal,← bounds.2 (f i) (List.mem_ofFn.mpr ⟨i,rfl⟩)]
    exact value_lt _
  have da : d.natAbs ≤ 2^A ∧ a.natAbs ≤ 2^A := by
    have := Nat.lt_two_pow_self (n:=A); dsimp [A] at *; omega
  have mag : y.natAbs = d.natAbs^M*c*a.natAbs := by simp [y,Int.natAbs_mul,Int.natAbs_pow]
  have size : y.natAbs ≤ 2^(A*(M+1)+n) := by
    rw [mag]
    calc
      _ ≤ (2^A)^M * 2^n * 2^A := by gcongr <;> first | exact da.1 | exact da.2
      _ = _ := by rw [← pow_mul,← pow_add,← pow_add]; congr 1; ring
  have tiny : 2*y.natAbs < 2^w := by
    dsimp [w]; rw [pow_add]; norm_num
    have := Nat.two_pow_pos (A*(M+1)+n)
    omega
  obtain ⟨z,eq⟩ := congr
  have diff : (2:ℤ)^w ∣ y-x := by
    refine ⟨basis.repr z i,?_⟩
    have rel : (d^M*(c:ℤ)) • (1:R) - decodeCoordinates basis (List.ofFn f) = (2:ℤ)^w • z := by
      simpa only [zsmul_eq_mul,mul_one,Int.cast_pow,Int.cast_ofNat] using eq
    have h := congrArg (fun t => basis.repr t i) rel
    simp only [map_sub,map_smul,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul,
      decodeCoordinates,basis.repr_sum_self] at h
    exact h
  have readMag := magnitude raw tiny (by exact_mod_cast diff)
  rw [eval]
  simp only [tally_length]
  rw [readMag,mag]
  have den : 0 < d.natAbs^M*a.natAbs := by have ha : a ≠ 0 := hi; positivity
  rw [show d.natAbs^M*c*a.natAbs = c*(d.natAbs^M*a.natAbs) by ring,Nat.mul_div_cancel _ den]

end
end OAI.Computability.MultitapeWeakETH.TemplateArithmetic
