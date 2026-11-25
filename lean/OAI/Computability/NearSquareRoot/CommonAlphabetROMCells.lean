import OAI.Computability.NearSquareRoot.ScheduleProgramReindexRun

/-! # Additive physical-space overhead of a numbered ROM

The two physical program heads visit intervals bounded in terms of the table size.
The simulated bank contributes its original distinct cells with coefficient one.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal.Reindex
open IntegerMultiplication TM
variable {A Q I : Type} [Finite A] [Fintype I] {m : ℕ}

/-- One loader and interpreter execute every generated finite table. Reindexing
the candidate control preserves its output tape, visited-cell bound and step count.
The loader starts with the generated table on its source ROM. -/
theorem install_numbered_sharp (enum : Q ≃ Fin m) (entry : Q) (blank : A)
    (candidate : Rule A Q I) (reads : List (I → A)) (complete : ∀ r, r ∈ reads)
    (d : I → Tape A) {z : Config A Q I} {t S : ℕ}
    (run : Trace (TM.advance candidate) ⟨entry,d⟩ t z) (halt : TM.advance candidate z = none)
    (space : VisitsAtMost candidate ⟨entry,d⟩ t S) :
    let code := encode enum entry candidate reads
    let K := 4*(code.length+1)
    let init := TapeSequence.relabel Sum.inl (Loader.initial blank code d)
    ∃ n finish, n ≤ 2*code.length+3 + K*(t+1) ∧
      Trace (TM.advance (Loader.installAndRun blank)) init n finish ∧
      TM.advance (Loader.installAndRun blank) finish = none ∧
      (∀ i, finish.tape (.inl i) = dataCell (z.tape i)) ∧
      VisitsAtMost (Loader.installAndRun blank) init n
        (Fintype.card I + 2*(code.length+1) + (S + 2*(code.length+2*K+1))) := by
  let e := numbering enum entry
  have hm := Nat.zero_lt_of_lt (enum entry).isLt
  have hinit : TapeSequence.relabel e (⟨entry,d⟩ : Config A Q I) =
      (⟨⟨0,hm⟩,d⟩ : Config A (Fin m) I) := by simp [e,TapeSequence.relabel]
  have hr := trace e candidate run
  have hs := visits e candidate _ _ _ space
  rw [hinit] at hr hs
  exact Loader.install_halting_space_sharp hm blank (rule e candidate) reads complete d
    hr ((halt_iff e candidate z).2 halt) hs

end Universal.Reindex

end NearSquareRoot
end Computability
end OAI
