import OAI.Computability.MultitapeWeakETH.GridProgram

/-! # Computing the exact real-power cutoff by integer comparisons -/

namespace OAI.Computability.MultitapeWeakETH.DyadicBudget

open IntegerMultiplication Code Strip Staff Carry

private abbrev reg : Regime (Tally × Tally) := ⟨size,send,Dom.base _⟩

/-- Decide whether the positive candidate index belongs to the search prefix. -/
private def test (d : ℕ) (q : Tally × Tally) := decide ((q.2.length+1)^d ≤ q.1.length^(d-1))

private theorem test_poly (d : ℕ) : Poly (test d) := by
  have v : Realizes reg (fun q => q.1.length) := by
    change Poly (fun q : Tally × Tally => tally q.1.length)
    simpa only [recover_tally] using (Easy.fst (X:=Tally) (Y:=Tally)).poly
  have j : Realizes reg (fun q => q.2.length) := by
    change Poly (fun q : Tally × Tally => tally q.2.length)
    simpa only [recover_tally] using (Easy.snd (X:=Tally) (Y:=Tally)).poly
  have lim := (Figure.of_spoken v).repeated (Realizes.fix (d-1))
  have pow := (Figure.of_spoken (j.plus (Realizes.fix 1))).repeated (Realizes.fix d)
  obtain ⟨flag,hf,correct⟩ := lim.compare_ pow
  have prog : Poly flag := hf
  convert prog.compose Iter.negate.poly using 1
  funext q
  specialize correct q
  unfold test
  cases e : flag q <;> simp_all

def searchWidth (d : ℕ) (q : Tally) :=
  ruler (((Iter.lineup q).map (fun j => test d (q,j))).filter id)

theorem searchWidth_poly (d : ℕ) : Poly (searchWidth d) :=
  ((Poly.identity.pair Iter.poly_line).compose (Poly.push [] [] (test_poly d))).compose
    ((Poly.filter id Poly.identity).compose (Easy.ruler Easy.identity).poly)

private theorem count_prefix (N m : ℕ) :
    ((List.ofFn (fun i : Fin N => decide (i.val < m))).filter id).length = min N m := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,List.filter_append,List.length_append]
    change ((List.ofFn (fun i : Fin n => decide (i.val < m))).filter id).length +
      ([decide (n < m)].filter id).length = _
    rw [ih]
    by_cases h : n < m <;> simp [h] <;> omega

private theorem test_iff (d N j : ℕ) (hd : 1<d) :
    (j+1)^d ≤ N^(d-1) ↔ j < ⌊(N:ℝ)^(1-1/(d:ℝ))⌋₊ := by
  have pos : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have exp : 1-1/(d:ℝ) = ((d-1:ℕ):ℝ)*(d:ℝ)⁻¹ := by
    rw [Nat.cast_sub (by omega : 1≤d),Nat.cast_one]
    field_simp
  rw [Nat.lt_iff_add_one_le,Nat.le_floor_iff (by positivity),exp,Real.rpow_mul (by positivity),
    Real.rpow_natCast,Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) pos,Real.rpow_natCast]
  norm_cast

/-- The polynomial tape calculation produces the precise natural floor in
the outer history, shared assignment and local search bounds. -/
theorem searchWidth_eq (d N : ℕ) (hd : 1<d) :
    searchWidth d (tally N) = tally ⌊(N:ℝ)^(1-1/(d:ℝ))⌋₊ := by
  let m := ⌊(N:ℝ)^(1-1/(d:ℝ))⌋₊
  have le : m ≤ N := by
    by_cases hN : N=0
    · subst N
      have pos : (0:ℝ) < 1-1/(d:ℝ) := by
        have h : (1:ℝ)<d := by exact_mod_cast hd
        have := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) h
        linarith
      simp only [m,Nat.cast_zero]
      rw [Real.zero_rpow pos.ne',Nat.floor_zero]
    · exact Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN)
        (sub_le_self _ (by positivity)))
  rw [← recover_tally (searchWidth d (tally N))]
  simp only [searchWidth,ruler_length,Iter.lined,List.map_ofFn,Function.comp_def,test,tally_length,
    test_iff d N _ hd,count_prefix]
  exact congrArg tally (Nat.min_eq_right le)

end OAI.Computability.MultitapeWeakETH.DyadicBudget
