import OAI.Computability.NearSquareRoot.ScheduleArithmeticClocks
import OAI.Computability.NearSquareRoot.ScheduleStagingComparisons

/-! # Releasing calibrated arithmetic source files as one uniform multiplier -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate
open GeneratorSyntax CommonAlphabet Filter
noncomputable section

/-- Effective arithmetic files with a common source-register bound yield the
literal uniform multiplication theorem once one fixed tuple attains each requested
clock and uses linear space. The finite law does not test these comparisons.
Index zero runs schoolbook multiplication on the same public input and output banks. -/
theorem ArenaFiles.uniformMultiplicationSpec {T S : ℕ → ℕ → ℕ}
    (f : ArenaFiles T S) (calibration : Calibrated T S) : UniformMultiplicationSpec := by
  classical
  let a := f.positiveSlots
  obtain ⟨d,C,ctl⟩ := StagingLiteral.controller
  let I := Option (Pack.FixedTapes a.registers)
  let B := StagingProtection.Cell d
  let J := StagingFallback.Axes d I
  let _ : Fintype J := Fintype.ofFinite J
  let Y := Universal.Tag B J
  let _ : Fintype Y := Fintype.ofFinite Y
  let _ : Nonempty Y := ⟨.origin⟩
  obtain ⟨M,hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fintype.card_pos (α := Y)))
  let enum : Y ≃ Fin (M+1) := (Fintype.equivFin Y).trans (finCongr hm)
  obtain ⟨_,_,_,digits⟩ := a.digits
  choose E _ all using digits
  let Tr (i n : ℕ) := E i*(T i.pred n+n+1)
  let Sr (i n : ℕ) := E i*(S i.pred n+n+1)
  have good (h : ℕ) : ∃ (j L : ℕ) (A : ℝ), 0 ≤ A ∧
      (∀ᶠ n : ℕ in atTop, Sr (j+1) n ≤ L*(n+1)) ∧
      ∀ᶠ n : ℕ in atTop, (Tr (j+1) n : ℝ) ≤ A*n*logScale n^((1:ℝ)/2+1/(h+2:ℝ)) := by
    obtain ⟨j,A,L,hA,ht,hs⟩ := calibration.digit_bounds E h
    exact ⟨j,L,A,hA,hs,ht⟩
  exact (Generator.Staged.arenaPrograms a d C).uniformMultiplicationSpec
    (StagingFallback.ports d I) enum (Generator.Staged.arenaPrograms_effective a d C enum)
    (Generator.Staged.comparisons d C ctl a.digitStates a.digitRule a.digitStart Tr Sr all good)

/-- The complete fixed-tape pipeline releases a single machine when the same
arithmetic tuple simultaneously controls its live arena and three varying transforms. -/
theorem uniformMultiplicationSpec_of_transports (K : ℕ → ℕ) (hK : Computable K)
    (hN : ∀ i, 2 ≤ K i) (hv : ∀ i (x : LargeInput (K i)), Directory x.val.width)
    (plan : ∀ i x, Plan (hv i x)) (c : ℕ → Clocks) (A : ℕ → ℕ → ℕ)
    (ha : ∀ i n, n ≤ A i n) (ops : EffectiveTransportsAt K hv plan c A)
    (good : ∀ j : ℕ, ∃ i : ℕ, (∃ L : ℕ, ∀ᶠ n in atTop, A i n ≤ L*(n+1)) ∧
      ∀ clock ∈ [(c i).route,(c i).forward,(c i).inverse], ∃ H : ℝ, 0 < H ∧
        ∀ᶠ n in atTop, (clock n : ℝ) ≤ H*n*logScale n^((1:ℝ)/2+1/(j+2:ℝ))) :
    UniformMultiplicationSpec := by
  obtain ⟨f⟩ := arenaFiles_of_transports K hK hN hv plan c A ha ops
  apply f.uniformMultiplicationSpec
  intro j
  obtain ⟨i,arena,clocks⟩ := good j
  obtain ⟨⟨L,space⟩,H,pos,time⟩ := good_arena_clock (c i) (A i) (by positivity) arena clocks
  exact ⟨i,H,L,pos.le,time,space⟩

end
end FixedCandidate

end NearSquareRoot
end Computability
end OAI
