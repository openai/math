import OAI.Computability.NearSquareRoot.ScheduleGeneratorFamily
import OAI.Computability.NearSquareRoot.ScheduleGeneratorInputRun

/-! # Running searched templates from the scheduler's unary parameter tape -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorInputRun
open IntegerMultiplication TM Turing.ToPartrec Universal
variable {A I : Type} [Finite A] [Fintype I] {M : ℕ}

/-- The public source tape starts at an arbitrary address. Every candidate tape
is simulated exactly, and the source head and contents are restored. -/
def RunsOnUnary {Q : Type} (blank : A) (mark : Letter A I) (c : Code)
    (enum : Tag A I ≃ Fin (M+1)) (i : ℕ) (entry : Q) (candidate : Rule A Q I) (E : ℕ) : Prop :=
  ∀ (H : ℤ) (d : I → Tape A) {z : Config A Q I} {t S : ℕ},
    Trace (advance candidate) ⟨entry,d⟩ t z → advance candidate z = none →
    VisitsAtMost candidate ⟨entry,d⟩ t S →
    ∃ n finish, n ≤ E*(t+1) ∧
      Trace (advance (rule blank mark c enum)) (initial blank mark c H i d) n finish ∧
      advance (rule blank mark c enum) finish = none ∧
      finish.tape (.inl ()) = Generator.Input.source (.inl blank) mark H i ∧
      (∀ l, finish.tape (.inr (.inr (.inl l))) = dataCell (z.tape l)) ∧
      VisitsAtMost (rule blank mark c enum) (initial blank mark c H i d) n (E*(S+1))

/-- The complete search, program emission, loading and interpretation includes
preparing the generator input from the actual unary parameter. -/
theorem compile_unary {Q : Type} (blank : A) (mark : Letter A I) (distinct : Sum.inl blank ≠ mark)
    (c : Code) (enum : Tag A I ≃ Fin (M+1)) (i : ℕ) (entry : Q) (candidate : Rule A Q I)
    (E : ℕ) (realizes : GeneratorPipeline.RunsCandidate blank c enum i entry candidate E) :
    RunsOnUnary blank mark c enum i entry candidate (E+8*i+18+2*(Fintype.card I+7)) := by
  intro H d z t S tr halt vis
  obtain ⟨n,finish,time,sim,halted,data,space⟩ := realizes d tr halt vis
  obtain ⟨sim',halted',space'⟩ := run blank mark distinct c enum H i d sim halted space
  refine ⟨_,_,?_,sim',halted',rfl,data,?_⟩
  · rw [Nat.mul_add] at time ⊢
    nlinarith only [time, Nat.le_add_left E (8*i+18+2*(Fintype.card I+7)),
      Nat.zero_le ((8*i+18+2*(Fintype.card I+7))*t)]
  · obtain ⟨cells,card,cover⟩ := space'
    exact ⟨cells,by nlinarith [Nat.zero_le ((8*i+18+2*(Fintype.card I+7))*S)],cover⟩

theorem searched_machine (blank : A) (mark : Letter A I) (distinct : Sum.inl blank ≠ mark)
    (enum : Tag A I ≃ Fin (M+1)) (reads : List (I → A)) (complete : ∀ r, r ∈ reads)
    (test : ℕ → ℕ → Bool) (ht : Computable₂ test) (hex : ∀ i, ∃ k, test i k = true)
    {Q : ℕ → ℕ → Type} {N : ℕ → ℕ → ℕ} (entries : ∀ i k, Q i k)
    (numbers : ∀ i k, Q i k ≃ Fin (N i k)) (machines : ∀ i k, Rule A (Q i k) I)
    (emits : Computable₂ (fun i k => GeneratorPipeline.symbolWord enum
      (Reindex.encode (numbers i k) (entries i k) (machines i k) reads))) :
    ∃ (c : Code) (pick E : ℕ → ℕ), Computable pick ∧ Finite (Control c M) ∧ Finite (Index I) ∧
      ∀ i, test i (pick i) = true ∧ (∀ k < pick i, test i k = false) ∧ 0 < E i ∧
        RunsOnUnary blank mark c enum i (entries i (pick i)) (machines i (pick i)) (E i) := by
  obtain ⟨c,pick,cost,eff,finite,spec⟩ := GeneratorPipeline.searched_family blank enum reads
    complete test ht hex entries numbers machines emits
  let : Finite (GeneratorPipeline.Control c M) := finite
  let : Finite (GeneratorPipeline.Index I) := GeneratorPipeline.finite_indices
  refine ⟨c,pick,(fun i => cost i+8*i+18+2*(Fintype.card I+7)),eff,inferInstance,inferInstance,fun i => ?_⟩
  rcases spec i with ⟨good,least,pos,exec⟩
  exact ⟨good,least,by dsimp; omega,compile_unary blank mark distinct c enum i _ _ _ exec⟩

end GeneratorInputRun

end NearSquareRoot
end Computability
end OAI
