import OAI.Computability.NearSquareRoot.ShortWordSpace

/-! # Unbounded finite prefixes of a deterministic tape computation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal
open IntegerMultiplication TM
variable {A Q I : Type}

/-- The rule admits a finite execution of each length from the given tapes. -/
def RunsForever (m : Rule A Q I) (x : Config A Q I) : Prop :=
  ∀ t : ℕ, ∃ y, Trace (advance m) x t y

theorem runsForever_iff (m : Rule A Q I) (x : Config A Q I) :
    RunsForever m x ↔ ¬∃ t y, Trace (advance m) x t y ∧ advance m y = none := by
  constructor
  · rintro forever ⟨t,y,run,halt⟩
    obtain ⟨z,long⟩ := forever (t+1)
    obtain ⟨w,first,tail⟩ := trace_split long (show t ≤ t+1 by omega)
    rw [← trace_endpoint_unique run first] at tail
    have last : Trace (advance m) y 1 z := by simpa using tail
    have dead {v : Config A Q I} {k : ℕ} (h : Trace (advance m) y k v) : k = 0 := by
      cases h with
      | nil => rfl
      | cons h _ => rw [halt] at h; contradiction
    exact Nat.one_ne_zero (dead last)
  · intro live n
    induction n with
    | zero => exact ⟨x,.nil _⟩
    | succ n ih =>
      obtain ⟨y,first⟩ := ih
      cases h : advance m y with
      | none => exact (live ⟨n,y,first,h⟩).elim
      | some z => exact ⟨z,first.trans (.single h)⟩

theorem runsForever_of_long {m : Rule A Q I} {x : Config A Q I}
    (long : ∀ n, ∃ t ≥ n, ∃ y, Trace (advance m) x t y) : RunsForever m x := by
  intro n
  obtain ⟨t,ht,y,run⟩ := long n
  obtain ⟨z,hz,_⟩ := trace_split run ht
  exact ⟨z,hz⟩

end Universal

end NearSquareRoot
end Computability
end OAI
