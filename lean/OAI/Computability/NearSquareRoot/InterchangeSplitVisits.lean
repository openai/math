import OAI.Computability.NearSquareRoot.VisitedCells

/-! # Space charge for linear-time scans

Across `t` transitions a tape contributes at most one cell at each of the
`t+1` instants. Summing this bound over the fixed family of tapes applies to
the complete run, including setup, rewinds, and cleanup.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication

/-- Each tape contributes at most one visited cell per instant. -/
theorem visitsAtMost_of_step_count {A Q I : Type} [Fintype I] (m : TM.Rule A Q I)
    (init : TM.Config A Q I) (steps : ℕ) :
    VisitsAtMost m init steps (Fintype.card I * (steps + 1)) := by
  classical
  let endpoint (u : Fin (steps + 1)) : TM.Config A Q I :=
    if h : ∃ c, Trace (TM.advance m) init u.val c then h.choose else init
  let position (p : I × Fin (steps + 1)) := (p.1, ((endpoint p.2).tape p.1).pos)
  refine ⟨Finset.univ.image position, ?_, ?_⟩
  · simpa using Finset.card_image_le (s := Finset.univ) (f := position)
  · intro u hu c hc i
    let v : Fin (steps + 1) := ⟨u, by omega⟩
    have h : ∃ d, Trace (TM.advance m) init v.val d := ⟨c, hc⟩
    have he : endpoint v = c := by
      dsimp only [endpoint]
      rw [dite_eq_left h]
      exact trace_endpoint_unique h.choose_spec hc
    exact Finset.mem_image.mpr ⟨(i, v), Finset.mem_univ _, by simp [position, he]⟩

end NearSquareRoot
end Computability
end OAI
