import OAI.Computability.BorderVNP.DiagonalCalendarNativeReaderExists
import OAI.Computability.BorderVNP.DiagonalPrimeFieldStretch

/-! # The signed native columns and the border stretch lemma -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Filter VPVNP

/-- Each fixed shortening gives one schedule for all sufficiently large
lengths, with the original paid scalars and the scalar entries of one cube.
The field chart and its charged reader are supplied after the threshold. -/
theorem paid_native_columns {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K]
    (G : PaidIdentity F D m) (φ : K →+* F) (q : ℕ) [CharP F q] (hm : 0 < m) :
    ∃ (cube : FixedCube K) (S : StretchSchedule), NativeColumns q G (φ ∘ cube.table) S := by
  obtain ⟨cube,_,S,_,scales,C,p,coeff,A₀,a,B₀,b₀,J,j,b,select⟩ := exists_frozen_execution_calendar G φ q hm
  refine ⟨cube,b.physical,?_⟩
  intro f hf c k
  obtain ⟨addr,pow,lengths⟩ := select 1 f hf c k 1
  filter_upwards [lengths] with n length
  dsimp only
  intro l eqn
  subst n
  obtain ⟨cal,oper⟩ := length
  intro ord common chart
  let : Fact common.p.Prime := ⟨common.prime⟩
  let : Algebra (ZMod common.p) chart.E := ZMod.algebra _ _
  intro _ _ _ reader charged
  let : Fact (8 ≤ (8 : ℕ)) := ⟨le_rfl⟩
  rw [oper.grid.link_eq]
  exact cal.nativeReaderExists oper (by decide) chart reader charged

end Diagonal

namespace ProvedStretch

open Crossing Diagonal Filter MvPolynomial

/-- The algebraic closure of the scalar field satisfies the border stretch
implication for each fixed paid shortening. -/
theorem over_field (K : Type) [Field K] (q : ℕ) [CharP K q] : Rate.PrimeFieldStretch K := by
  apply Rate.primeFieldStretch_of_native_columns K q
  intro D hD m hm G
  let : NeZero D := ⟨by omega⟩
  obtain ⟨cube,S,cols⟩ := paid_native_columns G (algebraMap K (AlgebraicClosure K)) q hm
  exact ⟨Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width,inferInstance,
    algebraMap K (AlgebraicClosure K) ∘ cube.table,S,cols⟩

/-- Theorem 3.2 in the ground-field image closure, from the original
profile shortening of Section 3.1. -/
theorem profile (K : Type) [Field K] (q : ℕ) [CharP K q]
    (shortening : HasProfileShortening (AlgebraicClosure K)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, (2 : ℝ)^((n : ℝ)^ε) ≤
      groundBorderSize n (map (Int.castRingHom (AlgebraicClosure K)) (Pstar n)) :=
  (Rate.primeFieldStretch_iff_profile K).mp (over_field K q) shortening

/-- The characteristic-zero prime field used in the uniform rate transfer. -/
theorem rational : Rate.PrimeFieldStretch ℚ := over_field ℚ 0

/-- The positive-characteristic prime fields used in the same transfer. -/
theorem prime (p : ℕ) (hp : p.Prime) : letI : Fact p.Prime := ⟨hp⟩; Rate.PrimeFieldStretch (ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  exact over_field (ZMod p) p

end ProvedStretch

end BorderVNP
end Computability
end OAI
