import OAI.Optimization.LinearProgramming.Compression.InnerNativeWords

/-! A sign row presented by the fixed binary service describes an affine form of its
proxy coordinates. The same row semantics apply to rational or real input magnitudes. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open OracleSpec _root_.OAI.Optimization.LinearProgramming.Lattice SignType
open scoped BigOperators

noncomputable def coordinateSign {d : ℕ} (v : Fin d → ℝ) (row : Fin (d+1) → ℤ) : SignType :=
  sign (dotProduct (realCoordinates row) (Fin.snoc v (1 : ℝ)))

def matchesCoordinates {g : ℕ} (N : ℕ) (v : Fin (g+1) → ℝ) (o : WordOracle) : Prop :=
  ∀ h (a : Fin ((g+1)+1) → ℤ), permitted N a → o h (signRowWord a) =
    signReply (orderOfSign (coordinateSign v a))

theorem coordinateSign_test {d : ℕ} (v : Fin d → ℝ) (negative : (Fin d → ℤ) → ℤ → Bool)
    (hn : ∀ a c, negative a c=true ↔ requestForm v a+c<0) :
    (fun a => decide (0 ≤ coordinateSign v a)) = affineCommitReply negative := by
  funext a
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,coordinateSign,sign_nonneg_iff]
  exact (affineCommitReply_correct v negative hn a).symm

theorem coordinateSign_pad {g : ℕ} (v : Fin (g+1) → ℝ) (a : Fin (g+1) → ℤ) :
    coordinateSign v (padEpochQuery a) = coordinateSign (fun i => v i.castSucc) a := by
  simp only [coordinateSign,dotProduct,realCoordinates,Fin.sum_univ_castSucc,padEpochQuery,
    Fin.snoc_castSucc,Fin.snoc_last,Int.cast_zero,zero_mul,add_zero]

theorem epochNegative_correct {g : ℕ} (v : Fin (g+1) → ℝ) (negative : (Fin (g+1) → ℤ) → ℤ → Bool)
    (hn : ∀ a c, negative a c=true ↔ requestForm v a+c<0) (a : Fin g → ℤ) (c : ℤ) :
    negative (Fin.snoc a 0) c=true ↔ requestForm (fun i => v i.castSucc) a+c<0 := by
  simpa only [requestForm,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,Int.cast_zero,zero_mul,add_zero]
    using hn (Fin.snoc a 0) c

def roundZFor {d : ℕ} (M : ℕ) (negative : (Fin d → ℤ) → ℤ → Bool) : Fin (d+1) → ℤ :=
  SignQueries.run (affineCommitReply negative) (lllRoundingProgram (d+1) M)

theorem sharedGamma_for {g : ℕ} (N : ℕ) (negative : (Fin (g+1) → ℤ) → ℤ → Bool) :
    sharedEpochCommit N g negative = normalizeCommit (roundZFor (epochRadius N g) (fun a c => negative (Fin.snoc a 0) c)) := rfl

theorem matches_coordinates_of_magnitudes {g N : ℕ} (mag : Fin (g+1) → ℚ) (hm : ∀ i,0<mag i)
    (o : WordOracle) (ho : «matches» N mag o) :
    matchesCoordinates N (generatorProxy (manuscriptProxyFuel N) (paperRadius N+7) mag) o := by
  intro hist a ha
  rw [coordinateSign,← generatorSign_correct _ _ mag hm a,cached_sign_order]
  exact ho hist a ha

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
