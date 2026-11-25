import OAI.Computability.NearSquareRoot.ScheduleProgramLoaderRun
import OAI.Computability.NearSquareRoot.ScheduleProgramReindex

/-! # Installing a generated transition table with arbitrary finite control -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal.Reindex

open IntegerMultiplication TM
variable {A Q I : Type} [Finite A] [Fintype I] {m : ℕ}

/-- Construct the finite table in row order from a given state enumeration. -/
def encode (enum : Q ≃ Fin m) (q : Q) (candidate : Rule A Q I) (reads : List (I → A)) :=
  program (rule (numbering enum q) candidate) reads

/-- One loader and interpreter execute every generated finite table. Reindexing
the candidate control preserves its output tape, visited-cell bound and step count.
The loader starts with the generated table on its source ROM. -/
theorem install_numbered (enum : Q ≃ Fin m) (entry : Q) (blank : A)
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
        (Fintype.card I + 2*(code.length+1) + (S*(2*K+1) + 2*(code.length+2*K+1))) := by
  let e := numbering enum entry
  have hm := Nat.zero_lt_of_lt (enum entry).isLt
  have hinit : TapeSequence.relabel e (⟨entry,d⟩ : Config A Q I) =
      (⟨⟨0,hm⟩,d⟩ : Config A (Fin m) I) := by simp [e,TapeSequence.relabel]
  have hr := trace e candidate run
  have hs := visits e candidate _ _ _ space
  rw [hinit] at hr hs
  exact Loader.install_halting_space hm blank (rule e candidate) reads complete d
    hr ((halt_iff e candidate z).2 halt) hs

/-- Every finite pointed control admits a numbering placing its entry in row zero. -/
theorem install_finite [Finite Q] (entry : Q) (blank : A)
    (candidate : Rule A Q I) (reads : List (I → A)) (complete : ∀ r, r ∈ reads)
    (d : I → Tape A) {z : Config A Q I} {t S : ℕ}
    (run : Trace (TM.advance candidate) ⟨entry,d⟩ t z) (halt : TM.advance candidate z = none)
    (space : VisitsAtMost candidate ⟨entry,d⟩ t S) :
    let code := program (rule (finiteNumbering entry) candidate) reads
    let K := 4*(code.length+1)
    let init := TapeSequence.relabel Sum.inl (Loader.initial blank code d)
    ∃ n finish, n ≤ 2*code.length+3 + K*(t+1) ∧
      Trace (TM.advance (Loader.installAndRun blank)) init n finish ∧
      TM.advance (Loader.installAndRun blank) finish = none ∧
      (∀ i, finish.tape (.inl i) = dataCell (z.tape i)) ∧
      VisitsAtMost (Loader.installAndRun blank) init n
        (Fintype.card I + 2*(code.length+1) + (S*(2*K+1) + 2*(code.length+2*K+1))) :=
  install_numbered (Finite.equivFin Q) entry blank candidate reads complete d run halt space

end Universal.Reindex

end NearSquareRoot
end Computability
end OAI
