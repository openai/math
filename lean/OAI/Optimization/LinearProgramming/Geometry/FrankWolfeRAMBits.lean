import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeRAM
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfePartialBits

/-! A polynomial bound for all rational registers in the primitive Frank–Wolfe program. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace FWRAM

open RAM Matrix
open scoped BigOperators Matrix

variable {n : Nat}

/-- An input-dimension bound for the rational registers in the terminal threshold computation. -/
def energyWidth (n : Nat) : Nat := 3 + 2 * (1000*(n+1))^2

theorem natRegister_bits_le (x : Nat) : RAM.ratBits (x:ℚ) ≤ 3+x := by
  simpa [RAM.ratBits, show Nat.log2 1 = 0 by decide] using
    Nat.add_le_add_left (Nat.log2_le_self x) 3

private theorem scaleSq_natCast (n : Nat) :
    (((1000*n)^2 : Nat) : ℚ) = ((1000:ℚ)*n)^2 := by
  calc
    (((1000*n)^2 : Nat) : ℚ) = ((1000*n:Nat):ℚ)^2 := map_pow (Nat.castRingHom ℚ) _ _
    _ = ((1000:ℚ)*n)^2 := congrArg (fun z : ℚ => z^2) (map_mul (Nat.castRingHom ℚ) 1000 n)

theorem energyThreshold_bits (n : Nat) (hn : 0<n) : RAM.ratBits (energyThreshold (K:=ℚ) n) ≤
    energyWidth n := by
  let d := (1000*n)^2
  have hd : 0<d := by dsimp [d]; positivity
  have he : energyThreshold (K:=ℚ) n = (1:ℚ)/(d:ℚ) := by
    change (1/(1000*(n:ℚ)))^2 = 1/(((1000*n)^2:Nat):ℚ)
    rw [div_pow,one_pow,scaleSq_natCast]
  have hrep : energyThreshold (K:=ℚ) n = Rat.divInt 1 (d:ℤ) := by
    simpa [Rat.divInt_eq_div] using he
  have hdvd : (energyThreshold (K:=ℚ) n).den ∣ d := by
    have hh := Rat.den_dvd (1:ℤ) (d:ℤ)
    rw [← hrep] at hh
    exact_mod_cast hh
  have ha : |energyThreshold (K:=ℚ) n| ≤ 1 := by
    rw [he, abs_of_nonneg (by positivity : 0 ≤ (1:ℚ)/(d:ℚ))]
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast hd
  apply ratBits_of_unit ha
  apply (Nat.le_of_dvd hd hdvd).trans
  exact Nat.pow_le_pow_left (Nat.mul_le_mul_left 1000 (Nat.le_succ n)) 2

theorem energy_constants_bits (n : Nat) (hn : 0<n) :
    RAM.ratBits (0 : ℚ) ≤ energyWidth n ∧ RAM.ratBits (1 : ℚ) ≤ energyWidth n ∧
    RAM.ratBits (1000 : ℚ) ≤ energyWidth n ∧
    RAM.ratBits (1000 * (n : ℚ)) ≤ energyWidth n ∧
    RAM.ratBits ((1000 * (n : ℚ))^2) ≤ energyWidth n ∧
    RAM.ratBits (energyThreshold (K:=ℚ) n) ≤ energyWidth n := by
  have cap (k : Nat) (h : k ≤ 2*(1000*(n+1))^2) : RAM.ratBits (k:ℚ) ≤ energyWidth n :=
    (natRegister_bits_le k).trans (Nat.add_le_add_left h 3)
  refine ⟨?_, ?_, ?_, ?_, ?_, energyThreshold_bits n hn⟩
  · exact cap 0 (by omega)
  · exact cap 1 (by ring_nf; omega)
  · exact cap 1000 (by ring_nf; omega)
  · simpa only [Nat.cast_mul,Nat.cast_ofNat] using cap (1000*n) (by ring_nf; omega)
  · rw [← scaleSq_natCast]
    exact cap _ (by ring_nf; omega)

/-- The dimension-polynomial width bound for the actual rational inputs in round `p`.
The gradient in the matrix-vector buffer is compared with zero and may be any rational. -/
theorem fwRound_update_bits {n : Nat} (Q : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n)
    (p : Nat) (g : ℚ) :
    let z := (fwArray Q i p).get j
    let a := 2/((p:ℚ)+2)
    let d := cellCorner (i:Nat) (j:Nat) g-z
    let width := updateWidth (p+2) (4*(p+1)*(p+2))
    RAM.ratBits d ≤ width ∧ RAM.ratBits (a*d) ≤ width ∧
      RAM.ratBits (cellValue i j a g z) ≤ width := by
  dsimp only
  let a : ℚ := 2/((p:ℚ)+2)
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    refine ⟨by dsimp [a]; positivity, ?_⟩
    apply (div_le_one (by positivity)).mpr
    have : (0:ℚ) ≤ p := Nat.cast_nonneg _
    linarith
  have had : a.den ≤ p+2 := by
    have hre : a = Rat.divInt 2 ((p+2:Nat):ℤ) := by simp [a,Rat.divInt_eq_div]
    have hd := Rat.den_dvd 2 ((p+2:Nat):ℤ)
    rw [← hre] at hd
    exact Nat.le_of_dvd (by omega) (by exact_mod_cast hd)
  have hb := (inLabelBox_iff _ _).mp (fwIterate_mem Q i p)
  rw [← fwArray_correct] at hb
  have hden : ((fwArray Q i p).get j).den ≤ 4*(p+1)*(p+2) := by
    cases p with
    | zero =>
      rw [fwArray_correct]
      change (fwLower (K:=ℚ) i j).den ≤ 8
      by_cases h : j = i
      · simp only [fwLower,h,ite_true]
        exact quarter_den_le.trans (by decide)
      · simp [fwLower,h]
    | succ p =>
      refine (fwArray_reduced_size Q i (p+1) (Nat.succ_pos _) j).1.trans ?_
      gcongr <;> omega
  exact updateCell_bits i j a g _ _ _ ha (hb.1 j) had hden

/-- Sum of bounds for the matrix products, moves, terminal threshold and scalar counters. -/
def labelBitWidth (n B : Nat) : Nat :=
  B + fwGradientWidth n B +
    updateWidth (fwRounds n+2) (4*(fwRounds n+1)*(fwRounds n+2)) +
    energyWidth n + 8*(fwRounds n+n+8000004)

theorem labelBitWidth_polynomial (n B : Nat) :
    labelBitWidth n B ≤ RAM.polyBound (10^50) 15 (n+B) := by
  have hn : n ≤ n+B := by omega
  have hb : B ≤ n+B := by omega
  have mono : labelBitWidth n B ≤ labelBitWidth (n+B) (n+B) := by
    unfold labelBitWidth fwGradientWidth updateWidth energyWidth fwRounds
    gcongr
  refine mono.trans ?_
  generalize n+B = x
  unfold labelBitWidth fwGradientWidth updateWidth energyWidth fwRounds RAM.polyBound
  ring_nf
  omega

private theorem stepFraction_bits (p : Nat) : RAM.ratBits (2/(p+2 : ℚ)) ≤ 3+2*(p+2) := by
  let a : ℚ := 2/(p+2 : ℚ)
  have ha : |a| ≤ 1 := by
    rw [abs_of_nonneg (by dsimp [a]; positivity : 0 ≤ a)]
    apply (div_le_one (by positivity)).mpr
    have : (0 : ℚ) ≤ p := Nat.cast_nonneg _
    linarith
  apply ratBits_of_unit ha
  have hre : a = Rat.divInt 2 ((p+2:Nat):ℤ) := by simp [a,Rat.divInt_eq_div]
  have hd := Rat.den_dvd 2 ((p+2:Nat):ℤ)
  rw [← hre] at hd
  exact Nat.le_of_dvd (by omega) (by exact_mod_cast hd)

/-- Every scalar required by the uniform RAM construction lies within a bound in the
dimension and the maximum width of an input entry of the rational projection matrix. -/
theorem labelSafe_rational (Q : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (hs : Qᵀ=Q) (he : Q*Q=Q) (B : Nat) (hB : ∀ r j, RAM.ratBits (Q r j) ≤ B) :
    LabelSafe Q i (fun q => RAM.ratBits q ≤ labelBitWidth n B) := by
  let cap := labelBitWidth n B
  have scalar (k : Nat) (hk : k ≤ fwRounds n+n+8000004) : RAM.ratBits (k:ℚ) ≤ cap :=
    (natRegister_bits_le k).trans (by dsimp [cap,labelBitWidth]; omega)
  have dg : fwGradientWidth n B ≤ cap := by dsimp [cap,labelBitWidth]; omega
  have de : energyWidth n ≤ cap := by dsimp [cap,labelBitWidth]; omega
  have du (p : Nat) (hp : p ≤ fwRounds n) :
      updateWidth (p+2) (4*(p+1)*(p+2)) ≤ cap := by
    have hmono : updateWidth (p+2) (4*(p+1)*(p+2)) ≤
        updateWidth (fwRounds n+2) (4*(fwRounds n+1)*(fwRounds n+2)) := by
      unfold updateWidth
      gcongr
    exact hmono.trans (by dsimp [cap,labelBitWidth]; omega)
  have quarter : RAM.ratBits (1/4:ℚ) ≤ cap := by
    exact (ratBits_of_unit (by norm_num) quarter_den_le).trans (by dsimp [cap,labelBitWidth]; omega)
  have gradient (p : Nat) (hp : p ≤ fwRounds n) :
      GradientSafe (fun q => RAM.ratBits q ≤ cap) Q (fwIterate Q i p) := by
    obtain ⟨term,pre,_,_⟩ := fwGradient_bounds Q hs he i B hB p hp
    exact ⟨fun r j => (term r j).trans dg, fun r k hk => (pre r k hk).trans dg⟩
  obtain ⟨h0,h1,h1000,hscale,hsq,hτ⟩ := energy_constants_bits n i.pos
  obtain ⟨_,_,eterm,eprefix⟩ := fwGradient_bounds Q hs he i B hB (fwRounds n) le_rfl
  refine ⟨h0.trans de,h1.trans de,quarter,?_,?_,?_,gradient _ le_rfl,
    h1000.trans de,hscale.trans de,hsq.trans de,hτ.trans de,?_,?_⟩
  · intro j hj
    exact scalar j (by omega)
  · intro j
    have hj : j.val ≤ 3 := by omega
    have hpow : n ^ j.val ≤ n^3 := Nat.pow_le_pow_right i.pos hj
    have hc : 8000000*n^j.val ≤ fwRounds n := Nat.mul_le_mul_left _ hpow
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      scalar (8000000*n^j.val) (by omega)
  · intro p hp
    refine ⟨h0.trans de,quarter,h1.trans de,scalar 2 (by omega),?_,?_,
      scalar (p+1) (by omega),gradient p hp.le,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_ofNat] using scalar (p+2) (by omega)
    · exact (stepFraction_bits p).trans (by dsimp [cap,labelBitWidth]; omega)
    · intro j
      have hm := fwRound_update_bits Q i j p ((Q *ᵥ fwIterate Q i p) j)
      rw [fwArray_correct] at hm
      exact ⟨hm.1.trans (du p hp.le),hm.2.1.trans (du p hp.le),hm.2.2.trans (du p hp.le)⟩
  · intro j
    exact (eterm j).trans dg
  · intro k hk
    exact (eprefix k hk).trans dg

/-- Fully bounded primitive-instruction trace. The program and both explicit polynomials
are uniform across all dimensions and all rational projection matrices. -/
theorem labelProgram_rational_bounded (L : Layout n) (i : Fin n)
    (Q : Matrix (Fin n) (Fin n) ℚ) (hs : Qᵀ=Q) (he : Q*Q=Q) (m : Memory ℚ)
    (a : Addresses L i m) (hQ : ∀ r j : Fin n, m.data (L.matrix+r.val*n+j.val)=Q r j)
    (B : Nat) (hm : m.AllData (fun q => RAM.ratBits q ≤ B)) :
    ∃ k ≤ RAM.polyBound 500000000 5 n, ∃ t : Fin (k+1) → State ℚ,
      Trace labelProgram (m.atPC 0) k t ∧ (t (Fin.last k)).output=some 0 ∧
      (t (Fin.last k)).data 19=(if fwLabel Q i then 1 else 0) ∧
      ∀ j, RAM.scalarBound (RAM.polyBound (10^50) 15 (n+B)) (t j) := by
  have widthIn : B ≤ labelBitWidth n B := by unfold labelBitWidth; omega
  have hentry r j : RAM.ratBits (Q r j) ≤ B := by rw [← hQ r j]; exact hm _
  let P := fun q => RAM.ratBits q ≤ labelBitWidth n B
  have hstart : m.AllData P := fun j => (hm j).trans widthIn
  have hsafe := labelSafe_rational Q i hs he B hentry
  obtain ⟨k,hk,t,htr,hhalt,hval,hwidth⟩ := labelProgram_trace L i Q hs he m P hstart a hQ hsafe
  refine ⟨k,hk.trans (labelTime_polynomial n),t,htr,hhalt,?_,?_⟩
  · simpa [fwLabel,fwArray_correct,fwTolerance,energyThreshold] using hval
  · exact fun j r => (hwidth j r).trans (labelBitWidth_polynomial n B)

end FWRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
