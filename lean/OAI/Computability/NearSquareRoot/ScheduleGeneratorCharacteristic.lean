import OAI.Computability.NearSquareRoot.ScheduleGeneratorCode
import OAI.Computability.NearSquareRoot.InterchangeRecurrence

/-! # Effective choice of a data characteristic with strict exponent slack -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator

/-- Bounded trial division, including the two degenerate nonprime inputs. -/
theorem primrecPrime : PrimrecPred Nat.Prime := by
  have divisor : PrimrecRel fun d n : ℕ => n % d ≠ 0 ∨ d = 1 :=
    ((Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).not.or
      (Primrec.eq.comp Primrec.fst (Primrec.const 1))).primrecRel
  have check := (Primrec.nat_le.comp (Primrec.const 2) Primrec.id).and
    (divisor.forall_lt.comp Primrec.id Primrec.id)
  apply check.of_eq
  intro n
  simp [Nat.prime_def_lt,Nat.dvd_iff_mod_eq_zero,Classical.or_iff_not_imp_left]

/-- The finite template search can take the first prime strictly above
`6*(j+2)`. Its characteristic term lies below the midpoint between `1/2`
and the requested exponent `1/2 + 1/(j+2)`. -/
theorem choose_characteristic :
    ∃ p : ℕ → ℕ, Computable p ∧ ∀ j, (p j).Prime ∧ 2 < p j ∧
      (1:ℝ)/2 + (3*(p j : ℝ)-1)/(p j : ℝ)^2 < 1/2 + 1/(2*((j:ℝ)+2)) := by
  let test (j q : ℕ) := decide (q.Prime ∧ 6*(j+2) < q)
  have htest : Computable₂ test :=
    ((primrecPrime.comp Primrec.snd).and (Primrec.nat_lt.comp
      (Primrec.nat_mul.comp (Primrec.const 6) (Primrec.nat_add.comp Primrec.fst (Primrec.const 2)))
      Primrec.snd)).decide.to_comp
  have hex (j : ℕ) : ∃ p, test j p = true := by
    obtain ⟨p,large,prime⟩ := Nat.exists_infinite_primes (6*(j+2)+1)
    exact ⟨p,decide_eq_true ⟨prime,by omega⟩⟩
  obtain ⟨p,eff,hp⟩ := first_certificate test htest hex
  refine ⟨p,eff,fun j => ?_⟩
  obtain ⟨prime,large⟩ := of_decide_eq_true (hp j).1
  have pos : (0 : ℝ) < p j := by exact_mod_cast prime.pos
  have large' : 6*((j:ℝ)+2) < (p j : ℝ) := by exact_mod_cast large
  refine ⟨prime,by omega,add_lt_add_right ?_ _⟩
  apply (div_lt_div_iff₀ (sq_pos_of_pos pos) (by positivity)).mpr
  nlinarith [mul_lt_mul_of_pos_right large' pos,Nat.cast_nonneg (α := ℝ) j]

end Generator

end NearSquareRoot
end Computability
end OAI
