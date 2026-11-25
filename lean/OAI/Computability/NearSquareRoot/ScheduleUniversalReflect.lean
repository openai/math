import OAI.Computability.NearSquareRoot.CommonAlphabetROMCells
import OAI.Computability.NearSquareRoot.ScheduleForever

/-! # Divergence of a candidate on the generated finite-ROM interpreter -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal
open IntegerMultiplication TM

/-- A side change marks each simulated transition, so its physical duration is positive. -/
theorem interpret_trace_lower {A I : Type} [Finite A] [Finite I] {m : ℕ}
    (blank : A) (machine : Rule A (Fin m) I) (rs : List (I → A)) (complete : ∀ r, r ∈ rs)
    {x z : Config A (Fin m) I} {t : ℕ} (run : Trace (advance machine) x t z) (side : Bool) :
    ∃ u side', t ≤ u ∧ Trace (advance (rule blank)) (ready machine rs side x) u (ready machine rs side' z) := by
  induction run generalizing side with
  | nil => exact ⟨0,side,le_rfl,.nil _⟩
  | @cons x y z n step _ ih =>
    obtain ⟨v,_,hop⟩ := interpret_step blank machine rs complete step side
    have pos : 0 < v := by
      by_contra! he
      obtain rfl : v = 0 := by omega
      have eq := trace_endpoint_unique (Trace.nil (ready machine rs side x)) hop
      have diff := congrArg (fun w : Config (Letter A I) PC (Index I) => w.pc.1) eq
      change side = !side at diff
      cases side <;> contradiction
    obtain ⟨u,s,hu,tail⟩ := ih (!side)
    exact ⟨v+u,s,by omega,hop.trans tail⟩

/-- Every finite candidate prefix persists through data normalization and the
one-time finite installation. -/
theorem Loader.install_forever {A I : Type} [Finite A] [Fintype I] {m : ℕ} (hm : 0 < m)
    (blank : A) (machine : Rule A (Fin m) I) (rs : List (I → A)) (complete : ∀ r, r ∈ rs)
    (d : I → Tape A) (forever : RunsForever machine ⟨⟨0,hm⟩,d⟩) :
    let code := program machine rs
    RunsForever (installAndRun blank) (TapeSequence.relabel Sum.inl (initial blank code d)) := by
  let code := program machine rs
  dsimp only
  intro n
  obtain ⟨z,run⟩ := forever n
  obtain ⟨u,side,hu,walk⟩ := interpret_trace_lower blank machine rs complete run false
  have start : Universal.ready machine rs false ⟨⟨0,hm⟩,d⟩ =
      normalize (loadedConf blank code d false .seek 1 0) := by
    simp [Universal.ready, normalize_loaded,code]
  rw [start] at walk
  obtain ⟨w,hw,_⟩ := pull_trace walk
  have mount : (⟨(false,.seek),(Loader.ready blank code d).tape⟩ :
      Config (Letter A I) PC (Index I)) = loadedConf blank code d false .seek 1 0 := by
    rw [ready_tapes]
    rfl
  rw [← mount] at hw
  have first := TapeSequence.first_trace Loader.rule (Universal.rule blank) (false,.seek)
    (load_program blank machine rs d).1
  have hand := Trace.single (TapeSequence.handoff Loader.rule (Universal.rule blank) (false,.seek)
    (c := Loader.ready blank code d) (by rfl))
  have last := TapeSequence.second_trace Loader.rule (Universal.rule blank) (false,.seek) hw
  obtain ⟨c,shorter,_⟩ := trace_split ((first.trans hand).trans last)
    (show n ≤ 2*code.length+2+1+u by omega)
  exact ⟨c,shorter⟩

/-- A nonterminating numbered candidate remains nonterminating on the common loader. -/
theorem Reindex.install_numbered_forever {A Q I : Type} [Finite A] [Fintype I] {m : ℕ}
    (enum : Q ≃ Fin m) (entry : Q) (blank : A) (candidate : Rule A Q I)
    (reads : List (I → A)) (complete : ∀ r, r ∈ reads) (d : I → Tape A)
    (forever : RunsForever candidate ⟨entry,d⟩) :
    let code := encode enum entry candidate reads
    RunsForever (Loader.installAndRun blank) (TapeSequence.relabel Sum.inl (Loader.initial blank code d)) := by
  let e := numbering enum entry
  have hm := Nat.zero_lt_of_lt (enum entry).isLt
  apply Loader.install_forever hm blank (Reindex.rule e candidate) reads complete d
  have start : TapeSequence.relabel e (⟨entry,d⟩ : Config A Q I) =
      (⟨⟨0,hm⟩,d⟩ : Config A (Fin m) I) := by simp [e,TapeSequence.relabel]
  rw [←start]
  intro t
  obtain ⟨z,hr⟩ := forever t
  exact ⟨_,trace e candidate hr⟩

end Universal

end NearSquareRoot
end Computability
end OAI
