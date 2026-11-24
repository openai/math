import OAI.Computability.VPVNP.RAMExecution

/-!
# Exact choice streams of a burst RAM call

From fixed control and external memory, two successful streams of choices
cannot properly extend one another. The assertion is independent of their
instruction fuel. In particular, success on every bit pattern of a given
width determines the complete set of admissible streams.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*} {P : Program w C}

/-- A successful stream has no successful proper extension, even with a
different fuel allowance. Equality of streams forces equality of reports. -/
theorem execute_prefix_unique {f g : ℕ} {c : C} {m : Memory w} {bits suffix : List Bool}
    {r r' : Report w} (h : execute P f c m bits = some r)
    (h' : execute P g c m (bits ++ suffix) = some r') : suffix = [] ∧ r = r' := by
  induction f generalizing g c m bits r r' with
  | zero => simp [execute] at h
  | succ f ih =>
    cases g with
    | zero => simp [execute] at h'
    | succ g =>
      cases hs : P.step c with
      | reject => simp [execute, hs] at h
      | finish result =>
        cases bits <;> cases suffix <;> simp_all [execute]
      | branch next =>
        cases bits with
        | nil => simp [execute, hs] at h
        | cons b bs =>
          simp only [execute, hs, List.cons_append, Option.map_eq_some_iff] at h h'
          obtain ⟨s, hs, rfl⟩ := h
          obtain ⟨s', hs', rfl⟩ := h'
          obtain ⟨hz, rfl⟩ := ih hs hs'
          exact ⟨hz, rfl⟩
      | localStep next | read a next | write a v next =>
        simp only [execute, hs, Option.map_eq_some_iff] at h h'
        obtain ⟨s, hs, rfl⟩ := h
        obtain ⟨s', hs', rfl⟩ := h'
        obtain ⟨hz, rfl⟩ := ih hs hs'
        exact ⟨hz, rfl⟩

/-- If all length-`k` bit patterns return, every returning execution consumes
exactly `k` choices. Shorter patterns extend to length `k`, and longer patterns
have a prefix of that length. -/
theorem execute_length_of_complete {k f : ℕ} {c : C} {m : Memory w}
    (hfull : ∀ bs : List Bool, bs.length = k → ∃ g r', execute P g c m bs = some r')
    {bits : List Bool} {r : Report w} (h : execute P f c m bits = some r) : bits.length = k := by
  rcases (show bits.length < k ∨ bits.length = k ∨ k < bits.length by omega) with hlt | heq | hgt
  · let suffix := List.replicate (k - bits.length) false
    obtain ⟨g, r', h'⟩ := hfull (bits ++ suffix) (by simp [suffix]; omega)
    have hlen := congrArg List.length (execute_prefix_unique h h').1
    simp only [suffix, List.length_replicate, List.length_nil] at hlen
    omega
  · exact heq
  · obtain ⟨g, r', h'⟩ := hfull (bits.take k) (by simp [Nat.min_eq_left (Nat.le_of_lt hgt)])
    have ht : execute P f c m (bits.take k ++ bits.drop k) = some r := by simpa using h
    have hlen := congrArg List.length (execute_prefix_unique h' ht).1
    simp only [List.length_drop, List.length_nil] at hlen
    omega

/-- At a fixed fuel budget, sufficiency of all fixed-width tapes also proves
necessity of that width. -/
theorem exists_execute_iff_length {k f : ℕ} {c : C} {m : Memory w}
    (hfull : ∀ bs : List Bool, bs.length = k → ∃ r, execute P f c m bs = some r)
    (bits : List Bool) : (∃ r, execute P f c m bits = some r) ↔ bits.length = k :=
  ⟨fun ⟨_, h⟩ ↦ execute_length_of_complete (fun bs hb ↦ ⟨f, hfull bs hb⟩) h, hfull bits⟩

end BurstRAM

end VPVNP
end Computability
end OAI
