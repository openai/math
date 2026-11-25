import OAI.Computability.NearSquareRoot.ScheduleGeneratorExecution
import OAI.Computability.NearSquareRoot.ScheduleGeneratorCode
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Effective strict call-count comparisons and their physical search cost -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator
open IntegerMultiplication Turing.ToPartrec

/-- A finite template's call count per input is `calls/width`. A target exponent
`num/den` is tested entirely by powering integers. -/
def contractionTest (calls width arity num den : ℕ) :=
  decide (calls ^ den < width ^ den * arity ^ num)

theorem contractionTest_correct (calls width arity num den : ℕ) (hw : 0 < width) (hd : 0 < den) :
    contractionTest calls width arity num den = true ↔
      (calls : ℝ) / width < (arity : ℝ) ^ ((num : ℝ) / den) := by
  have wpos : 0 < (width : ℝ) := by exact_mod_cast hw
  have dpos : 0 < (den : ℝ) := by exact_mod_cast hd
  have scale : ((arity : ℝ) ^ ((num : ℝ) / den)) ^ den = (arity : ℝ) ^ num := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _), div_mul_cancel₀ _ dpos.ne',Real.rpow_natCast]
  unfold contractionTest
  rw [decide_eq_true_eq,div_lt_iff₀ wpos]
  have iffPow := pow_lt_pow_iff_left₀ (Nat.cast_nonneg (α := ℝ) calls)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg arity) ((num : ℝ) / den)) wpos.le) hd.ne'
  rw [← iffPow,mul_pow,scale,mul_comm]
  exact_mod_cast Iff.rfl

/-- Inclusive comparison for a stage's certified upper bound on main-swap calls. -/
def volumeTest (calls width arity num den : ℕ) :=
  decide (calls ^ den ≤ width ^ den * arity ^ num)

theorem volumeTest_correct (calls width arity num den : ℕ) (hw : 0 < width) (hd : 0 < den) :
    volumeTest calls width arity num den = true ↔
      (calls : ℝ) / width ≤ (arity : ℝ) ^ ((num : ℝ) / den) := by
  have wpos : 0 < (width : ℝ) := by exact_mod_cast hw
  have dpos : 0 < (den : ℝ) := by exact_mod_cast hd
  have scale : ((arity : ℝ) ^ ((num : ℝ) / den)) ^ den = (arity : ℝ) ^ num := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _), div_mul_cancel₀ _ dpos.ne',Real.rpow_natCast]
  unfold volumeTest
  rw [decide_eq_true_eq,div_le_iff₀ wpos]
  have iffPow := pow_le_pow_iff_left₀ (Nat.cast_nonneg (α := ℝ) calls)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg arity) ((num : ℝ) / den)) wpos.le) hd.ne'
  rw [← iffPow,mul_pow,scale,mul_comm]
  exact_mod_cast Iff.rfl

theorem primrecNatPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := by
  let step := fun a : ℕ => fun p : ℕ × ℕ => p.2*a
  have recursive : Primrec₂ step := (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂
  exact (Primrec.nat_rec (Primrec.const 1) recursive).of_eq (fun a n => by
    induction n with
    | zero => rfl
    | succ n ih => simpa [step,pow_succ] using congrArg (·*a) ih)

/-- The actual arithmetic subtest can be plugged into any computable enumeration
of candidate descriptions, including when the parameters depend on both indices. -/
theorem computable_contractionTest {X : Type*} [Primcodable X]
    {a b m p q : X → ℕ} (ha : Computable a) (hb : Computable b) (hm : Computable m)
    (hp : Computable p) (hq : Computable q) :
    Computable fun x => contractionTest (a x) (b x) (m x) (p x) (q x) := by
  exact Primrec.nat_lt.decide.to_comp.comp (primrecNatPow.to_comp.comp ha hq)
    (Primrec.nat_mul.to_comp.comp (primrecNatPow.to_comp.comp hb hq) (primrecNatPow.to_comp.comp hm hp))

theorem computable_volumeTest {X : Type*} [Primcodable X]
    {a b m p q : X → ℕ} (ha : Computable a) (hb : Computable b) (hm : Computable m)
    (hp : Computable p) (hq : Computable q) :
    Computable fun x => volumeTest (a x) (b x) (m x) (p x) (q x) := by
  exact Primrec.nat_le.decide.to_comp.comp (primrecNatPow.to_comp.comp ha hq)
    (Primrec.nat_mul.to_comp.comp (primrecNatPow.to_comp.comp hb hq) (primrecNatPow.to_comp.comp hm hp))

/-- The template search runs on four fixed tapes. One natural-number function records
its actual running time on each index. Program selection, validation and word
emission all run before the halt captured by the trace. -/
theorem searched_generation (test : ℕ → ℕ → Bool) (ht : Computable₂ test)
    (hex : ∀ i, ∃ k, test i k = true) (emit : ℕ → ℕ → List ℕ) (he : Computable₂ emit) :
    ∃ (c : Code) (select budget : ℕ → ℕ),
      Computable select ∧ (∀ i, test i (select i) = true ∧ ∀ k < select i, test i k = false) ∧
      ∀ i, let w := unaryInput i
        let z := finalCfg c w (emit i (select i))
        Trace (TM.advance (rule c)) (initial c w) (budget i) z ∧ TM.advance (rule c) z = none ∧
        VisitsAtMost (rule c) (initial c w) (budget i) (4*(2*budget i+1)) := by
  obtain ⟨pick,hp,valid⟩ := first_certificate test ht hex
  obtain ⟨c,hc⟩ := exists_unary_list_code _ (he.comp Computable.id hp)
  have H (i : ℕ) := code_execution c (unaryInput i) (emit i (pick i)) (Part.eq_some_iff.mp (hc i))
  choose T run halt space using H
  exact ⟨c,pick,T,hp,valid,fun i => ⟨run i,halt i,space i⟩⟩

end Generator

end NearSquareRoot
end Computability
end OAI
