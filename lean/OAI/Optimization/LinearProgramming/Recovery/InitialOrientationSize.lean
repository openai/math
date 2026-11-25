import OAI.Optimization.LinearProgramming.Recovery.InitialPairCost
import OAI.Optimization.LinearProgramming.NormalSubspace.InputBits

/-! All entries of the first complementary pair are charged to the original LP
input. The subsequent marked call receives a single scalar-height polynomial. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialOrientation

open Matrix RAM RAM.Callable OracleSpec Geometry Polynomial

noncomputable def width (solver : NormalSubspace.Spec) : Polynomial ℕ :=
  InitialPair.sourceWidthPolynomial +
    solver.height.comp (X+1+(X+1)^2*InitialPair.sourceWidthPolynomial)+3

theorem pair_encoded_length {K : Type} {k s n : ℕ} (D : Matrix (Fin k) (Fin n) K) (E : Matrix (Fin s) (Fin n) K)
    (dims : k+s=n) : (encodedGramInput D++encodedGramInput E).length=n^2 := by
  subst n
  simp only [List.length_append,length_encodedGramInput,pow_two,Nat.add_mul]

theorem pair_data_length {k s n : ℕ} (D : Matrix (Fin k) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (dims : k+s=n) : (MinorLog.entries D++MinorLog.entries E).length=n^2 := by
  simpa only [NormalSubspace.gramEntries] using pair_encoded_length D E dims

private theorem pair_data_size {k s n B : ℕ} (D : Matrix (Fin k) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (dims : k+s=n) (hd : ∀ i j,ratBits (D i j) ≤ B) (he : ∀ i j,ratBits (E i j) ≤ B) :
    k+s+((MinorLog.entries D++MinorLog.entries E).map ratBits).sum ≤ n+n^2*B := by
  subst n
  exact NormalSubspace.inputSize_le D E hd he

theorem width_bounds {m d k s : ℕ} (solver : NormalSubspace.Spec)
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m→ℚ) (F : Matrix (Fin k) (Fin (m+1)) ℚ)
    (R : Matrix (Fin s) (Fin (m+1)) ℚ) (dims : k+s=m+1)
    (entriesF : ∀ i j,ratBits (F i j) ≤ InitialPair.fragmentWidth m d (max 3 (totalBits (lpInput A b))))
    (entriesR : ∀ i j,ratBits (R i j) ≤ InitialPair.fragmentWidth m d (max 3 (totalBits (lpInput A b)))) :
    let W := (width solver).eval (m+d+totalBits (lpInput A b))
    InitialPair.fragmentWidth m d (max 3 (totalBits (lpInput A b))) ≤ W ∧ 3 ≤ W ∧
    solver.height.eval (k+s+((MinorLog.entries F++MinorLog.entries R).map ratBits).sum) ≤ W := by
  let x := m+d+totalBits (lpInput A b)
  have raw := InitialPair.rawWidth_le A b
  have nX : m+1 ≤ x+1 := by dsimp [x];omega
  have bits := pair_data_size F R dims entriesF entriesR
  have size : k+s+((MinorLog.entries F++MinorLog.entries R).map ratBits).sum ≤
      x+1+(x+1)^2*InitialPair.sourceWidthPolynomial.eval x :=
    bits.trans (Nat.add_le_add nX (Nat.mul_le_mul (Nat.pow_le_pow_left nX 2) raw))
  have solverBits := InitialPair.eval_le solver.height size
  change _ ≤ (width solver).eval x ∧ 3 ≤ (width solver).eval x ∧ _ ≤ (width solver).eval x
  simp only [width,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
  change InitialPair.fragmentWidth m d (max 3 (totalBits (lpInput A b))) ≤
    InitialPair.sourceWidthPolynomial.eval x at raw
  omega

end InitialOrientation
end Recovery
end LinearProgramming
end Optimization
end OAI
