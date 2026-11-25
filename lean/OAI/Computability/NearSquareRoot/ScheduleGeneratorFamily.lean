import OAI.Computability.NearSquareRoot.ScheduleGeneratorBounds
import OAI.Computability.NearSquareRoot.ScheduleGeneratorROMExecute

/-! # One physical generator and interpreter for a family of searched templates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorPipeline
open IntegerMultiplication TM Turing.ToPartrec Universal
variable {A I : Type} [Finite A] [Fintype I] {M : ℕ}

/-- At one candidate index the setup time and the costs per simulated
step and per visited cell are bounded by a single finite constant. -/
def RunsCandidate {Q : Type} (blank : A) (c : Code) (enum : Tag A I ≃ Fin (M+1))
    (i : ℕ) (entry : Q) (candidate : Rule A Q I) (E : ℕ) : Prop :=
  ∀ (d : I → Tape A) {z : Config A Q I} {t S : ℕ},
    Trace (advance candidate) ⟨entry,d⟩ t z → advance candidate z = none →
    VisitsAtMost candidate ⟨entry,d⟩ t S →
    ∃ n finish, n ≤ E*(t+1) ∧
      Trace (advance (rule blank c enum)) (initial blank c (Generator.unaryInput i) d) n finish ∧
      advance (rule blank c enum) finish = none ∧
      (∀ l, finish.tape (.inr (.inl l)) = dataCell (z.tape l)) ∧
      VisitsAtMost (rule blank c enum) (initial blank c (Generator.unaryInput i) d) n (E*(S+1))

/-- A computable table construction and terminating certificate search
give one finite physical program for the whole family. Its startup PC, control
set, tape set and alphabet are independent of the candidate index. -/
theorem searched_family (blank : A) (enum : Tag A I ≃ Fin (M+1))
    (reads : List (I → A)) (complete : ∀ r, r ∈ reads)
    (test : ℕ → ℕ → Bool) (ht : Computable₂ test) (hex : ∀ i, ∃ k, test i k = true)
    {Q : ℕ → ℕ → Type} {N : ℕ → ℕ → ℕ} (entries : ∀ i k, Q i k)
    (numbers : ∀ i k, Q i k ≃ Fin (N i k)) (machines : ∀ i k, Rule A (Q i k) I)
    (emits : Computable₂ (fun i k => symbolWord enum
      (Reindex.encode (numbers i k) (entries i k) (machines i k) reads))) :
    ∃ (c : Code) (pick E : ℕ → ℕ), Computable pick ∧ Finite (Control c M) ∧
      ∀ i, test i (pick i) = true ∧ (∀ k < pick i, test i k = false) ∧ 0 < E i ∧
        RunsCandidate blank c enum i (entries i (pick i)) (machines i (pick i)) (E i) := by
  obtain ⟨pick,eff,good⟩ := Generator.first_certificate test ht hex
  obtain ⟨c,em⟩ := Generator.exists_unary_list_code _ (emits.comp Computable.id eff)
  have h (i : ℕ) := run_numbered blank c enum (Generator.unaryInput i) (numbers i (pick i))
    (entries i (pick i)) (machines i (pick i)) reads complete (Part.eq_some_iff.mp (em i))
  choose E hE run using h
  exact ⟨c,pick,E,eff,finite_control _ _,fun i => ⟨(good i).1,(good i).2,hE i,run i⟩⟩

end GeneratorPipeline

end NearSquareRoot
end Computability
end OAI
