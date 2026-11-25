import OAI.Computability.NearSquareRoot.ScheduleStagingReject
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxDigitLiteral

/-! # Applying the common fenced controller to the effective literal digit family -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingLiteral

open IntegerMultiplication TM Code Bits Filter
open ChunkControl (Driver)
open ChunkTask ChunkLoop ChunkPhases

def Spec (d : Driver) (C : ℕ) : Prop := ∀ p : ChunkTask.Input,
  StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C Lea.answer p
    ((answer Lea.answer p).map Ltr.bit)

private theorem digits_width : StagingProduct.HasWidth Lea.answer := fun _ => Lea.date_length _
private theorem digits_correct : StagingProduct.Multiplies Lea.answer := fun a => Lea.value_answer a.property.1

/-- The controller and all data and tape types are selected before the
effective family of programs. -/
theorem controller : ∃ (d : Driver) (C : ℕ), Spec d C := by
  obtain ⟨d,C,ctl⟩ := StagingPhases.raw_controllers
  exact ⟨d,C,fun p => ctl Lea.answer p (answer_spec Lea.answer digits_correct p).1⟩

variable {T : ℕ → ℕ → ℕ} (f : FixedCandidate.LiteralFamily T)

noncomputable abbrev machine (d : Driver) (j : ℕ) :=
  StagingReject.successful d (f.digitRule j) (f.digitStart j)

/-- All reported halts of all literal programs return the integer product. -/
theorem sound (d : Driver) (C : ℕ) (ctl : Spec d C) (j : ℕ) (p : ChunkTask.Input)
    {t z} (run : Trace (advance (machine f d j)) (StagingProtection.initial d C p.n (input p)) t z)
    (halt : advance (machine f d j) z = none) :
    ∃ w, whole (StagingProtection.blank d) (w.map (StagingProtection.bit d)) (z.tape none) ∧
      w.length = 2*p.n ∧ bitValue w = bitValue p.x * bitValue p.y := by
  obtain ⟨_,_,_,dig⟩ := f.digits
  obtain ⟨E,_,runDigit⟩ := dig j
  exact ⟨_,StagingReject.sound d C Lea.answer p _ _ _ _ (ctl p) runDigit digits_width digits_correct run halt⟩

private theorem absorb (E : ℕ) (T : ℕ → ℕ) (e A : ℝ) (he : 0 ≤ e) (hA : 0 ≤ A)
    (ht : ∀ᶠ n : ℕ in atTop, (T n:ℝ) ≤ A*n*logScale n^e) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ((E*(T n+n+1) : ℕ) : ℝ) ≤ B*n*logScale n^e := by
  refine ⟨E*(A+2),by positivity,?_⟩
  filter_upwards [ht,eventually_ge_atTop (1:ℕ)] with n time hn
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 ≤ logScale n^e := Real.one_le_rpow (by unfold logScale; linarith [Real.log_nonneg hn']) he
  have lin : (n:ℝ) ≤ n*logScale n^e := by nlinarith
  push_cast
  rw [mul_assoc _ (n:ℝ),mul_assoc (E:ℝ),← mul_assoc (A:ℝ)] at *
  gcongr
  nlinarith

/-- For a selected literal program, one fixed split and cutoff suffice. All
physical heads remain in a linear strip with a coefficient independent of
the selected program, while the per-index time coefficient may vary. -/
theorem selected (d : Driver) (C : ℕ) (ctl : Spec d C) (j : ℕ) (e A : ℝ)
    (he : 0 ≤ e) (hA : 0 ≤ A) (ht : ∀ᶠ n : ℕ in atTop, (T j n : ℝ) ≤ A*n*logScale n^e) :
    ∃ k : ℕ, ∃ H : ℝ, 0 ≤ H ∧ ∀ᶠ n : ℕ in atTop, 2^k ≤ n ∧
      ∀ p : ChunkTask.Input, p.n = n → p.k = k → ∃ t y,
        ((t+1:ℕ):ℝ) ≤ H*n*logScale n^e ∧
        FencedRun (machine f d j) (fun _ => -(StagingOuter.radius C n : ℤ)) (fun _ => (StagingOuter.radius C n : ℤ))
          (StagingProtection.initial d C n (input p)) t y ∧ advance (machine f d j) y = none ∧
        whole (StagingProtection.blank d) ((answer Lea.answer p).map (StagingProtection.bit d)) (y.tape none) := by
  obtain ⟨_,_,_,dig⟩ := f.digits
  obtain ⟨E,_,runDigit⟩ := dig j
  obtain ⟨B,hB,te⟩ := absorb E (T j) e A he hA ht
  obtain ⟨k,H,hH,late⟩ := StagingProduct.selected d C Lea.answer _ _ _ _ ctl runDigit digits_width
    digits_correct E (Filter.Eventually.of_forall fun _ => le_rfl) e B he hB te
  refine ⟨k,H,hH,?_⟩
  filter_upwards [late] with n bound
  refine ⟨bound.1,?_⟩
  intro p np kp
  obtain ⟨t,ht,done⟩ := bound.2 p np kp
  obtain ⟨y,trace,halt,out⟩ := StagingReject.success d C Lea.answer _ _ p t done
  exact ⟨t,y,ht,np ▸ trace,halt,out⟩

end StagingLiteral

end NearSquareRoot
end Computability
end OAI
